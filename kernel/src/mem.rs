pub mod slab;
pub mod virt;

use crate::dsa::{HasPinpoint, Pinpoint, ReprC};
use crate::lock::GuardLock;
use crate::mem::Error::{InvalidPageStart, PageNotAllocatable};
use crate::uart;
use core::convert::Into;
use core::sync::atomic::Ordering::Relaxed;
use hw::{DRAM_SIZE, DRAM_START};
use wrapper::{Address, Bytes};

/// The collection of current free pages that their [Pinpoint]s are circularly linked.
static FREE_PAGES: GuardLock<Page> = GuardLock::new(Page {
    pinpoint: Pinpoint::new(),
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
    let head = head_page.pinpoint();
    let head_ptr: *mut Pinpoint = head;
    head.link1.store(head_ptr, Relaxed);
    head.link2.store(head_ptr, Relaxed);
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
    // Acquire lock before freeing the page
    let mut head_page = FREE_PAGES.lock();

    // Fill the page with junk to catch dangling refs
    const JUNK: u8 = 0xf0;
    memset(start, JUNK, PAGE_SIZE);

    let head = head_page.pinpoint();
    let next = unsafe {
        let ptr = head.link2.load(Relaxed);
        ptr.as_mut().unwrap()
    };

    let mut new_page = Page {
        pinpoint: Pinpoint::new(),
    };
    new_page.pinpoint().link1.store(head, Relaxed);
    new_page.pinpoint().link2.store(next, Relaxed);

    let new_page_ptr: *mut Page = start.into();
    unsafe {
        new_page_ptr.write(new_page);
    }

    let new_next = unsafe { (&mut *new_page_ptr).pinpoint() };
    head.link2.store(new_next, Relaxed);
    next.link1.store(new_next, Relaxed);

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
    let head = head_page.pinpoint();

    let no_free_page = head.link2.load(Relaxed) == (head as *mut Pinpoint);
    if no_free_page {
        return Err(Error::OutOfMemory);
    }

    let pinpoint = unsafe {
        let ptr = head.link2.load(Relaxed);
        ptr.as_mut().unwrap()
    };
    let new_next = unsafe {
        let ptr = pinpoint.link2.load(Relaxed);
        ptr.as_mut().unwrap()
    };
    head.link2.store(new_next, Relaxed);
    new_next.link1.store(head, Relaxed);

    let result = (pinpoint as *const Pinpoint).into();
    unsafe {
        let page: *mut Page = (pinpoint as *mut Pinpoint).cast();
        page.drop_in_place();
    }
    Ok(result)
}

#[repr(C)]
struct Page {
    pinpoint: Pinpoint,
}

impl ReprC for Page {}

impl HasPinpoint for Page {
    fn pinpoint(&mut self) -> &mut Pinpoint {
        &mut self.pinpoint
    }
}

#[derive(Debug)]
enum Error {
    InvalidPageStart,
    PageNotAllocatable,
    OutOfMemory,
}
