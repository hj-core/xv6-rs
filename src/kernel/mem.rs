use crate::kernel::lock::GuardLock;
use crate::kernel::mem::Error::InvalidPagePointer;
use crate::kernel::uart;
use crate::machine::{DRAM_SIZE, DRAM_START};
use crate::wrapper::{Address, Bytes};
use core::convert::Into;
use core::ptr::null;

static mut FREE_PAGES: GuardLock<Page> = GuardLock::new(Page { next: null() });

const DRAM_END_EXCLUSIVE: Address = Address(DRAM_START.0 + (DRAM_SIZE.0 << 20) as u64);
const PAGE_SIZE: Bytes = Bytes(4096);

struct Page {
    pub next: *const Page,
}

pub fn initialize() {
    uart::busy_print_str("- Configuring physical memories... ");
    initialize_free_pages();
    uart::busy_print_str("Done!\n");
}

fn initialize_free_pages() {
    let mut page = first_valid_page();
    while free_page(page).is_ok() {
        page = unsafe { page.byte_add(PAGE_SIZE.0) };
    }
}

fn first_valid_page() -> *const Page {
    let start: *const u8 = allocatable_start().into();
    let align_offset = start.align_offset(PAGE_SIZE.0);
    unsafe { start.byte_add(align_offset).cast() }
}

fn allocatable_start() -> Address {
    extern "C" {
        #[link_name = "link_end"]
        static indirect_addr: u8;
    }
    Address(&raw const indirect_addr as u64)
}

#[allow(static_mut_refs)]
fn free_page(page: *const Page) -> Result<bool, Error> {
    if !is_allocatable(page.into()) || !is_valid_page_start(page.into()) {
        return Err(InvalidPagePointer);
    }
    // Fill page with junk to catch dangling refs
    memset(page.into(), 0xf0, PAGE_SIZE);

    let result = unsafe { &mut *page.cast_mut() };
    let mut head = unsafe { FREE_PAGES.lock() };
    result.next = head.next;
    head.next = result;
    Ok(true)
}

fn is_allocatable(addr: Address) -> bool {
    allocatable_start().0 <= addr.0 && addr.0 < DRAM_END_EXCLUSIVE.0
}

fn is_valid_page_start(addr: Address) -> bool {
    addr.0 % (PAGE_SIZE.0 as u64) == 0 && (addr + PAGE_SIZE).0 <= DRAM_END_EXCLUSIVE.0
}

fn memset(start: Address, value: u8, size: Bytes) {
    let start: *const u8 = start.into();
    for i in 0..size.0 {
        unsafe { *start.add(i).cast_mut() = value };
    }
}

#[derive(Debug)]
enum Error {
    InvalidPagePointer,
}
