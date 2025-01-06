pub mod virt;

use crate::lock::GuardLock;
use crate::mem::Error::{InvalidPagePointer, PageNotAllocatable};
use crate::uart;
use core::convert::Into;
use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;
use core::sync::atomic::Ordering::{Relaxed, Release};
use hw::{DRAM_SIZE, DRAM_START};
use wrapper::{Address, Bytes};

static FREE_PAGES: GuardLock<Page> = GuardLock::new(Page {
    next: AtomicPtr::new(null_mut()),
});

const DRAM_END_EXCLUSIVE: Address = Address(DRAM_START.0 + (DRAM_SIZE.0 << 20) as u64);
const PAGE_SIZE: Bytes = Bytes(4096);

struct Page {
    pub next: AtomicPtr<Page>,
}

pub fn initialize() {
    uart::busy_print_str("-> Initializing physical memories... ");
    initialize_free_pages();
    uart::busy_print_str("Done!\n");
}

fn initialize_free_pages() {
    let alloc_start = allocatable_start();
    let align_offset = (alloc_start.0 as *const u8).align_offset(PAGE_SIZE.0);

    let mut page_start = alloc_start + Bytes(align_offset);
    while free_page(page_start).is_ok() {
        page_start = page_start + PAGE_SIZE;
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
        return Err(InvalidPagePointer);
    }
    if !is_allocatable(start) {
        return Err(PageNotAllocatable);
    }
    // Fill page with junk to catch dangling refs
    memset(start.into(), 0xf0, PAGE_SIZE);

    let head = FREE_PAGES.lock();
    let old_next = head.next.load(Relaxed);
    let new_next = unsafe {
        let page: *mut Page = start.into();
        page.as_mut().unwrap().next.store(old_next, Relaxed);
        page
    };
    head.next.store(new_next, Relaxed);
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
    let head = FREE_PAGES.lock();
    if head.next.load(Relaxed).is_null() {
        return Err(Error::NoAllocatablePage);
    }

    let old_next = head.next.load(Relaxed);
    let old_page = unsafe { old_next.as_mut().unwrap() };
    let new_next = old_page.next.load(Relaxed);
    old_page.next.store(null_mut(), Relaxed);
    head.next.store(new_next, Release);
    Ok(old_next.into())
}

#[derive(Debug)]
enum Error {
    InvalidPagePointer,
    PageNotAllocatable,
    NoAllocatablePage,
}
