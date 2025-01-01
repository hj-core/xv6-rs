use crate::kernel::lock::GuardLock;
use crate::machine::{DRAM_SIZE_IN_MB, DRAM_START};
use core::ptr::null;

const DRAM_END_EXCLUSIVE: u64 = DRAM_START + ((DRAM_SIZE_IN_MB as u64) << 20);
const PAGE_SIZE_IN_BYTE: usize = 4096;
static mut FREE_PAGES: GuardLock<Page> = GuardLock::new(Page { next: null() });

struct Page {
    pub next: *const Page,
}

pub fn initialize() {
    initialize_free_pages();
}

fn initialize_free_pages() {
    unsafe {
        let mut page = first_valid_page();
        while is_valid_page(page) {
            free_page(page);
            page = page.byte_add(PAGE_SIZE_IN_BYTE);
        }
    };
}

fn first_valid_page() -> *const Page {
    let start = allocatable_start() as *const u8;
    unsafe { start.byte_add(start.align_offset(PAGE_SIZE_IN_BYTE)).cast() }
}

fn allocatable_start() -> u64 {
    extern "C" {
        #[link_name = "link_end"]
        static indirect_addr: u8;
    }
    &raw const indirect_addr as u64
}

fn is_valid_page(page: *const Page) -> bool {
    let addr = page as u64;
    addr % PAGE_SIZE_IN_BYTE as u64 == 0 && allocatable_start() <= addr && addr < DRAM_END_EXCLUSIVE
}

#[allow(static_mut_refs)]
fn free_page(page: *const Page) {
    assert!(is_valid_page(page));
    // Fill page with junk to catch dangling refs
    memset(page.cast(), 0xf0, PAGE_SIZE_IN_BYTE);

    unsafe {
        let mut head = FREE_PAGES.lock();
        (*page.cast_mut()).next = head.next;
        head.next = page;
    }
}

fn memset(start: *const u8, x: u8, size: usize) {
    unsafe {
        for i in 0..size {
            *start.add(i).cast_mut() = x;
        }
    }
}
