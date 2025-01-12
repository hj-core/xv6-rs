pub mod slab;
pub mod virt;

use crate::dsa::ListNode;
use crate::lock::GuardLock;
use crate::mem::Error::{InvalidPageStart, PageNotAllocatable};
use crate::{uart, HasHole, ReprC};
use core::convert::Into;
use core::ptr::null_mut;
use core::sync::atomic::Ordering::Relaxed;
use hw::{DRAM_SIZE, DRAM_START};
use wrapper::{Address, Bytes};

/// The collection of current free pages that their holes are circularly linked.
static FREE_PAGES: GuardLock<Page> = GuardLock::new(Page {
    hole: ListNode::new(),
});

const DRAM_END_EXCLUSIVE: Address = Address(DRAM_START.0 + DRAM_SIZE.0 as u64);
const PAGE_SIZE: Bytes = Bytes(4096);

pub fn initialize() {
    uart::busy_print_str("-> Initializing physical memories... ");
    initialize_free_pages();
    uart::busy_print_str("Done!\n");
}

fn initialize_free_pages() {
    // Link the head circularly
    let mut head_page = FREE_PAGES.lock();
    let head = head_page.hole();
    let head_ptr: *mut ListNode = head;
    head.prev.store(head_ptr, Relaxed);
    head.next.store(head_ptr, Relaxed);
    drop(head_page); // Release the lock

    let alloc_start = allocatable_start();
    let align_offset = (alloc_start.0 as *const u8).align_offset(PAGE_SIZE.0);

    let mut start = alloc_start + Bytes(align_offset);
    while free_page(start).is_ok() {
        start = start + PAGE_SIZE;
    }
}

fn allocatable_start() -> Address {
    extern "C" {
        #[link_name = "link_end"]
        static addr_as_value: u8;
    }
    Address(&raw const addr_as_value as u64)
}

fn free_page(start: Address) -> Result<bool, Error> {
    if !is_valid_page(start) {
        return Err(InvalidPageStart);
    }
    if !is_allocatable(start) {
        return Err(PageNotAllocatable);
    }
    // Fill page with junk to catch dangling refs
    memset(start.into(), 0xf0, PAGE_SIZE);

    let mut head_page = FREE_PAGES.lock();
    let head = head_page.hole();
    let next = unsafe {
        let ptr = head.next.load(Relaxed);
        ptr.as_mut().unwrap()
    };
    let new = unsafe {
        let ptr: *mut ListNode = start.into();
        ptr.as_mut().unwrap()
    };

    new.next.store(next, Relaxed);
    new.prev.store(head, Relaxed);
    next.prev.store(new, Relaxed);
    head.next.store(new, Relaxed);
    Ok(true)
}

fn is_valid_page(start: Address) -> bool {
    start.0 % (PAGE_SIZE.0 as u64) == 0 && (start + PAGE_SIZE).0 <= DRAM_END_EXCLUSIVE.0
}

fn is_allocatable(addr: Address) -> bool {
    allocatable_start().0 <= addr.0 && addr.0 < DRAM_END_EXCLUSIVE.0
}

fn memset(start: Address, value: u8, size: Bytes) {
    let start: *mut u8 = start.into();
    for i in 0..size.0 {
        unsafe { *start.add(i) = value };
    }
}

fn allocate_page() -> Result<Address, Error> {
    let mut head_page = FREE_PAGES.lock();
    let head = head_page.hole();
    if head.next.load(Relaxed) == head {
        return Err(Error::OutOfMemory);
    }

    let result = unsafe {
        let ptr = head.next.load(Relaxed);
        ptr.as_mut().unwrap()
    };
    let next_next = unsafe {
        let ptr = result.next.load(Relaxed);
        ptr.as_mut().unwrap()
    };
    head.next.store(next_next, Relaxed);
    next_next.prev.store(head, Relaxed);

    result.prev.store(null_mut(), Relaxed);
    result.next.store(null_mut(), Relaxed);
    Ok((result as *mut ListNode).into())
}

#[repr(C)]
struct Page {
    hole: ListNode,
}

impl ReprC for Page {}

impl HasHole for Page {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}

#[derive(Debug)]
enum Error {
    InvalidPageStart,
    PageNotAllocatable,
    OutOfMemory,
}
