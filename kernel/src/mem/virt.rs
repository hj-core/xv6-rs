// Use the Sv39 scheme (3-level 512-entry page table).

use crate::mem::{is_valid_page, DRAM_END_EXCLUSIVE, PAGE_SIZE};
use crate::{mem, uart};
use core::ops::Add;
use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;
use core::sync::atomic::Ordering::{Acquire, Release};
use hw;
use hw::plic::PLIC_MMIO_BASE;
use hw::plic::PLIC_MMIO_SIZE;
#[cfg(target_arch = "riscv64")]
use hw::riscv64;
use hw::uart::UART0_MMIO_BASE;
use hw::DRAM_START;
use wrapper::{Address, Bytes};

static KERNEL_ROOT_TABLE: AtomicPtr<PageTable> = AtomicPtr::new(null_mut());
const TABLE_SIZE: usize = 1 << 9;

#[cfg(target_arch = "riscv64")]
pub fn initialize() {
    uart::busy_print_str("-> Initializing virtual memories... ");
    configure_kernel_page_table();
    uart::busy_print_str("Done!\n");
}

#[cfg(target_arch = "riscv64")]
fn configure_kernel_page_table() {
    initialize_kernel_root_table();
    kernel_map_uart_pages();
    kernel_map_plic_pages();
    kernel_map_text_pages();
    kernel_map_data_pages();
}

fn initialize_kernel_root_table() {
    let ptr = PageTable::new().unwrap();
    KERNEL_ROOT_TABLE.store(ptr, Release);
}

/// Direct map the uart0 page.
fn kernel_map_uart_pages() {
    kernel_direct_map_pages(UART0_MMIO_BASE, 1, PTE::BIT_R | PTE::BIT_W).unwrap();
}

/// Direct map the plic pages.
fn kernel_map_plic_pages() {
    assert_eq!(0, PLIC_MMIO_SIZE.0 % PAGE_SIZE.0);
    kernel_direct_map_pages(
        PLIC_MMIO_BASE,
        PLIC_MMIO_SIZE.0 / PAGE_SIZE.0,
        PTE::BIT_R | PTE::BIT_W,
    )
    .unwrap();
}

/// Direct map the kernel text pages.
fn kernel_map_text_pages() {
    let size = kernel_text_size();
    assert_eq!(0, size.0 % PAGE_SIZE.0);
    kernel_direct_map_pages(DRAM_START, size.0 / PAGE_SIZE.0, PTE::BIT_R | PTE::BIT_X).unwrap();
}

fn kernel_text_size() -> Bytes {
    let end_exclusive = kernel_text_end_exclusive();
    assert!(DRAM_START.0 <= end_exclusive.0);
    Bytes((end_exclusive.0 - DRAM_START.0) as usize)
}

fn kernel_text_end_exclusive() -> Address {
    extern "C" {
        #[link_name = "link_text_end"]
        static addr_as_value: u8;
    }
    (&raw const addr_as_value).into()
}

/// Direct Map all pages after kernel text.
fn kernel_map_data_pages() {
    let page0 = kernel_text_end_exclusive();
    let size = Bytes((DRAM_END_EXCLUSIVE.0 - page0.0) as usize);
    assert_eq!(0, size.0 % PAGE_SIZE.0);
    kernel_direct_map_pages(page0, size.0 / PAGE_SIZE.0, PTE::BIT_R | PTE::BIT_W).unwrap();
}

fn kernel_direct_map_pages(
    page0: Address,
    pages: usize,
    permissions: u64,
) -> Result<bool, mem::Error> {
    map_pages(
        KERNEL_ROOT_TABLE.load(Acquire),
        page0.into(),
        page0.into(),
        pages,
        permissions,
    )
}

/// Map continuous pages starting from page0_va and page0_pa.
fn map_pages(
    root_table: *mut PageTable,
    page0_va: VirtualAddress,
    page0_pa: PhysicalAddress,
    pages: usize,
    permissions: u64,
) -> Result<bool, mem::Error> {
    for i in 0..pages {
        map_page(
            root_table,
            page0_va + PAGE_SIZE * i,
            page0_pa + PAGE_SIZE * i,
            permissions,
        )?;
    }
    Ok(true)
}

/// Map page_va to page_pa.
fn map_page(
    root_table: *mut PageTable,
    page_va: VirtualAddress,
    page_pa: PhysicalAddress,
    permissions: u64,
) -> Result<bool, mem::Error> {
    if !is_valid_page(page_pa.into()) || !is_valid_page(page_va.into()) {
        return Err(mem::InvalidPageStart);
    }

    let root_table = unsafe { root_table.as_mut().unwrap() };
    let root_pte = root_table.read_allocate(page_va.vpn2() as usize)?;

    let inter_table: *mut PageTable = root_pte.get_table_start().into();
    let inter_table: &mut PageTable = unsafe { inter_table.as_mut().unwrap() };
    let inter_pte = inter_table.read_allocate(page_va.vpn1() as usize)?;

    let leaf_table: *mut PageTable = inter_pte.get_table_start().into();
    let leaf_table: &mut PageTable = unsafe { leaf_table.as_mut().unwrap() };

    let mut leaf_pte = PTE(0);
    leaf_pte.set_ppn(page_pa);
    leaf_pte.set_permissions(permissions);
    leaf_pte.mark_valid();
    leaf_table.0[page_va.vpn0() as usize] = leaf_pte;

    Ok(true)
}

#[cfg(target_arch = "riscv64")]
pub fn configure_cpu() {
    enable_paging(KERNEL_ROOT_TABLE.load(Acquire).into());
}

#[cfg(target_arch = "riscv64")]
fn enable_paging(root_table: PhysicalAddress) {
    riscv64::write_satp(riscv64::SATP_MODE_SV39 | root_table.ppn());
}

#[repr(transparent)]
struct PageTable([PTE; TABLE_SIZE]);

impl PageTable {
    fn new() -> Result<*mut PageTable, mem::Error> {
        let page = mem::allocate_page()?;
        // SAFETY:
        // * We have asserted that our PageTable fits into one page and is aligned.
        //   Furthermore, because both PageTable and PTE are repr(transparent),
        //   the layout of PageTable is the same as [u64; TABLE_SIZE].
        // * Therefore, writing the size of the PageTable bytes with 0 from the page's
        //   starting address is not unsafe.
        // * Although this writing may cause UB if there is any dangling reference,
        //   such references will still cause UB even if we don't write to them,
        //   and this function is not in a position to address such kinds of UB.
        // * Therefore, writing to the pointer is considered safe.
        unsafe {
            assert_eq!(
                PAGE_SIZE.0,
                size_of::<PageTable>(),
                "PageTable doesn't fit into one page."
            );
            assert_eq!(
                0,
                page.0 as usize % align_of::<PageTable>(),
                "PageTable isn't aligned at the page start."
            );

            let result: *mut PageTable = page.into();
            result.write_bytes(0, 1);
            Ok(result)
        }
    }

    /// Returns the entry at index, allocating one if necessary.
    fn read_allocate(&mut self, index: usize) -> Result<&mut PTE, mem::Error> {
        if self.0[index].is_valid() {
            return Ok(&mut self.0[index]);
        }

        let new_table = PageTable::new()?;
        let mut pte = PTE(0);
        pte.mark_valid();
        pte.set_ppn(PhysicalAddress(new_table as u64));

        self.0[index] = pte;
        Ok(&mut self.0[index])
    }
}

#[derive(Debug, Eq, PartialEq)]
#[repr(transparent)]
struct PTE(u64);

impl PTE {
    const BIT_V: u64 = 1 << 0; // Is this PTE valid
    const BIT_R: u64 = 1 << 1; // Read permission
    const BIT_W: u64 = 1 << 2; // Write permission
    const BIT_X: u64 = 1 << 3; // Execute permission
    const BIT_U: u64 = 1 << 4; // Whether accessible to user mode
    const BIT_G: u64 = 1 << 5; // Is a global mapping?
    const BIT_A: u64 = 1 << 6; // Accessed. Used in leaf PTE.
    const BIT_D: u64 = 1 << 7; // Dirty. Used In left PET.
    const BIT_RSW: u64 = 0b11 << 8; // Reserved for supervisor software.
    const MASK_PERMISSIONS: u64 = 0b11110;
    const MASK_PPN: u64 = 0xfff_ffff_ffff << 10;

    fn is_valid(&self) -> bool {
        self.0 & Self::BIT_V != 0
    }

    fn mark_valid(&mut self) {
        self.0 |= Self::BIT_V;
    }

    fn set_permissions(&mut self, permissions: u64) {
        self.0 &= !Self::MASK_PERMISSIONS;
        self.0 |= permissions & Self::MASK_PERMISSIONS;
    }

    fn set_ppn(&mut self, pa: PhysicalAddress) {
        self.0 &= !Self::MASK_PPN;
        self.0 |= pa.ppn() << 10;
    }

    fn get_table_start(&self) -> Address {
        Address(((self.0 & Self::MASK_PPN) << 2) as usize)
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct PhysicalAddress(u64);

impl PhysicalAddress {
    const MASK_PPN0: u64 = 0x1ff << 12;
    const MASK_PPN1: u64 = 0x1ff << 21;
    const MASK_PPN2: u64 = 0x3ff_ffff << 30;
    const MASK_PPN: u64 = 0xfff_ffff_ffff << 12;
    const MASK_OFFSET: u64 = 0xfff;

    fn ppn(&self) -> u64 {
        (self.0 & Self::MASK_PPN) >> 12
    }

    fn ppn0(&self) -> u64 {
        (self.0 & Self::MASK_PPN0) >> 12
    }

    fn ppn1(&self) -> u64 {
        (self.0 & Self::MASK_PPN1) >> 21
    }

    fn ppn2(&self) -> u64 {
        (self.0 & Self::MASK_PPN2) >> 30
    }

    fn offset(&self) -> u64 {
        self.0 & Self::MASK_OFFSET
    }
}

impl Add<Bytes> for PhysicalAddress {
    type Output = Self;

    fn add(self, rhs: Bytes) -> Self::Output {
        Self(self.0 + rhs.0 as u64)
    }
}

impl From<Address> for PhysicalAddress {
    fn from(addr: Address) -> Self {
        Self(addr.0 as u64)
    }
}

impl From<PhysicalAddress> for Address {
    fn from(pa: PhysicalAddress) -> Self {
        Self(pa.0 as usize)
    }
}

impl<T> From<*const T> for PhysicalAddress {
    fn from(ptr: *const T) -> Self {
        PhysicalAddress(ptr as u64)
    }
}

impl<T> From<*mut T> for PhysicalAddress {
    fn from(ptr: *mut T) -> Self {
        PhysicalAddress(ptr as u64)
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct VirtualAddress(usize);

impl VirtualAddress {
    const MASK_VPN0: usize = 0x1ff << 12;
    const MASK_VPN1: usize = 0x1ff << 21;
    const MASK_VPN2: usize = 0x1ff << 30;
    const MASK_OFFSET: usize = 0xfff;

    fn vpn0(&self) -> usize {
        (self.0 & Self::MASK_VPN0) >> 12
    }

    fn vpn1(&self) -> usize {
        (self.0 & Self::MASK_VPN1) >> 21
    }

    fn vpn2(&self) -> usize {
        (self.0 & Self::MASK_VPN2) >> 30
    }

    fn offset(&self) -> usize {
        self.0 & Self::MASK_OFFSET
    }
}

impl Add<Bytes> for VirtualAddress {
    type Output = Self;

    fn add(self, rhs: Bytes) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl From<Address> for VirtualAddress {
    fn from(addr: Address) -> Self {
        Self(addr.0)
    }
}

impl From<VirtualAddress> for Address {
    fn from(va: VirtualAddress) -> Self {
        Self(va.0)
    }
}

#[cfg(test)]
mod page_table_tests {
    use super::*;

    #[test]
    fn test_self_size() {
        assert_eq!(PAGE_SIZE.0, size_of::<PageTable>())
    }
}

#[cfg(test)]
mod pte_tests {
    use super::{PhysicalAddress, PTE};
    use wrapper::Address;

    #[test]
    fn test_self_size() {
        assert_eq!(8, size_of::<PTE>());
    }

    #[test]
    fn test_valid() {
        assert_valid(PTE(0x1));
        assert_valid(PTE(0xfff_0f05));
    }

    fn assert_valid(pte: PTE) {
        assert!(pte.is_valid(), "{pte:?}");
    }

    #[test]
    fn test_invalid() {
        assert_invalid(PTE(0x0));
        assert_invalid(PTE(0xfff_fffe));
    }

    fn assert_invalid(pte: PTE) {
        assert!(!pte.is_valid(), "{pte:?}");
    }

    #[test]
    fn test_mark_valid() {
        assert_mark_valid(PTE(0xfff_0002));
        assert_mark_valid(PTE(0xffff_fff3));
    }

    fn assert_mark_valid(mut pte: PTE) {
        pte.mark_valid();
        assert_valid(pte);
    }

    #[test]
    fn test_set_permissions() {
        let expected = PTE(0xffff_ff1e);
        let pte = PTE(0xffff_ff00);
        let permissions = PTE::BIT_U | PTE::BIT_X | PTE::BIT_W | PTE::BIT_R;
        assert_set_permissions(expected, pte, permissions);

        let expected = PTE(0xffff_fffd);
        let pte = PTE(0xffff_ffe7);
        let permission = PTE::BIT_U | PTE::BIT_X | PTE::BIT_W;
        assert_set_permissions(expected, pte, permission);

        let expected = PTE(0xffff_ff00);
        let pte = PTE(0xffff_ff1e);
        let permission = 0;
        assert_set_permissions(expected, pte, permission);

        let expected = PTE(0xffff_ff00);
        let pte = PTE(0xffff_ff1e);
        let permission = 0xffff_ff00;
        assert_set_permissions(expected, pte, permission);
    }

    fn assert_set_permissions(expected: PTE, mut pte: PTE, permission: u64) {
        pte.set_permissions(permission);
        assert_eq!(expected, pte, "{pte:?}");
    }

    #[test]
    fn test_set_ppn() {
        let expected = PTE(0xffc0_0000_0000_03ff);
        let pte = PTE(0xffff_ffff_ffff_ffff);
        let pa = PhysicalAddress(0);
        assert_set_ppn(expected, pte, pa);

        let expected = PTE(0x003f_ffff_ffff_fc00);
        let pte = PTE(0);
        let pa = PhysicalAddress(0xffff_ffff_ffff_ffff);
        assert_set_ppn(expected, pte, pa);

        let expected = PTE(0xf03f_ff0f_faff_ff0f);
        let pte = PTE(0xf01f_f72a_fb20_a70f);
        let pa = PhysicalAddress(0xf5ff_fc3f_ebff_f80c);
        assert_set_ppn(expected, pte, pa);
    }

    fn assert_set_ppn(expected: PTE, mut pte: PTE, pa: PhysicalAddress) {
        pte.set_ppn(pa);
        assert_eq!(expected, pte, "{pte:?}");
    }

    #[test]
    fn test_get_table_addr() {
        assert_get_table_addr(Address(0x667c618eca5000), PTE(0x10199f1863b2955e));
        assert_get_table_addr(Address(0x7cc9c901af1000), PTE(0x615f3272406bc736));
    }

    fn assert_get_table_addr(expected: Address, pte: PTE) {
        assert_eq!(expected, pte.get_table_start(), "{pte:?}");
    }
}

#[cfg(test)]
mod physical_address_tests {
    use super::PhysicalAddress as PA;

    #[test]
    fn test_ppn() {
        assert_ppn(0xa88e0658617, PA(0x76a88e0658617ceb));
        assert_ppn(0x99a852786a1, PA(0x0d99a852786a1154));
        assert_ppn(0xaaf67234ede, PA(0xa7aaf67234ede1a7));
        assert_ppn(0x87a89912421, PA(0x1687a89912421da8));
        assert_ppn(0xbab73216ece, PA(0xc5bab73216ece2d3));
    }

    fn assert_ppn(expected: u64, pa: PA) {
        assert_eq!(expected, pa.ppn(), "{pa:?}");
    }

    #[test]
    fn test_ppn0() {
        assert_ppn0(0x000, PA(0x00_0000));
        assert_ppn0(0x000, PA(0x00_00ff));
        assert_ppn0(0x000, PA(0x00_0fff));
        assert_ppn0(0x001, PA(0x00_1fff));
        assert_ppn0(0x0ab, PA(0x0a_bff0));
        assert_ppn0(0x1ff, PA(0x1f_f000));
        assert_ppn0(0x1ff, PA(0xffff_ffff_ffff_ffff));
    }

    fn assert_ppn0(expected: u64, pa: PA) {
        assert_eq!(expected, pa.ppn0(), "{pa:?}");
    }

    #[test]
    fn test_ppn1() {
        assert_ppn1(0x000, PA(0x0000_0000));
        assert_ppn1(0x000, PA(0x0000_ffff));
        assert_ppn1(0x000, PA(0x000f_ffff));
        assert_ppn1(0x001, PA(0x002f_ff00));
        assert_ppn1(0x055, PA(0x0ab0_ffab));
        assert_ppn1(0x1ff, PA(0x3fff_ffff));
        assert_ppn1(0x1ff, PA(0xffff_ffff_ffff_ffff));
    }

    fn assert_ppn1(expected: u64, pa: PA) {
        assert_eq!(expected, pa.ppn1(), "{pa:?}");
    }

    #[test]
    fn test_ppn2() {
        assert_ppn2(0x000_0000, PA(0x00_0000_0000_0000));
        assert_ppn2(0x000_0000, PA(0x00_0000_0fff_ffff));
        assert_ppn2(0x000_0000, PA(0x00_0000_3fff_ffff));
        assert_ppn2(0x000_0001, PA(0x00_0000_4fff_0f0f));
        assert_ppn2(0x000_03fd, PA(0x00_00ff_4fff_0f0f));
        assert_ppn2(0x3ff_ffff, PA(0xff_ffff_ffff_ffff));
        assert_ppn2(0x3ff_ffff, PA(0xffff_ffff_ffff_ffff));
    }

    fn assert_ppn2(expected: u64, pa: PA) {
        assert_eq!(expected, pa.ppn2(), "{pa:?}");
    }

    #[test]
    fn test_offset() {
        assert_offset(0x000, PA(0x0000));
        assert_offset(0x100, PA(0x0100));
        assert_offset(0xfff, PA(0x0fff));
        assert_offset(0xfff, PA(0xffff_ffff_ffff_ffff));
    }

    fn assert_offset(expected: u64, pa: PA) {
        assert_eq!(expected, pa.offset(), "{pa:?}");
    }
}

#[cfg(test)]
mod virtual_address_tests {
    use super::VirtualAddress as VA;

    #[test]
    fn test_vpn0() {
        assert_vpn0(0x000, VA(0x00_0000));
        assert_vpn0(0x000, VA(0x00_00ff));
        assert_vpn0(0x000, VA(0x00_0fff));
        assert_vpn0(0x001, VA(0x00_1fff));
        assert_vpn0(0x0ab, VA(0x0a_bff0));
        assert_vpn0(0x1ff, VA(0x1f_f000));
        assert_vpn0(0x1ff, VA(0xffff_ffff_ffff_ffff));
    }

    fn assert_vpn0(expected: usize, va: VA) {
        assert_eq!(expected, va.vpn0(), "{va:?}");
    }

    #[test]
    fn test_vpn1() {
        assert_vpn1(0x000, VA(0x0000_0000));
        assert_vpn1(0x000, VA(0x0000_ffff));
        assert_vpn1(0x000, VA(0x000f_ffff));
        assert_vpn1(0x001, VA(0x002f_ff00));
        assert_vpn1(0x055, VA(0x0ab0_ffab));
        assert_vpn1(0x1ff, VA(0x3fff_ffff));
        assert_vpn1(0x1ff, VA(0xffff_ffff_ffff_ffff));
    }

    fn assert_vpn1(expected: usize, va: VA) {
        assert_eq!(expected, va.vpn1(), "{va:?}");
    }

    #[test]
    fn test_vpn2() {
        assert_vpn2(0x000, VA(0x00_0000_0000));
        assert_vpn2(0x000, VA(0x00_0ff0_0ff0));
        assert_vpn2(0x000, VA(0x00_3fff_ffff));
        assert_vpn2(0x001, VA(0x00_4fff_ffff));
        assert_vpn2(0x03f, VA(0x0f_ffff_ffff));
        assert_vpn2(0x1ff, VA(0x7f_ffff_ffff));
        assert_vpn2(0x1ff, VA(0xffff_ffff_ffff_ffff));
    }

    fn assert_vpn2(expected: usize, va: VA) {
        assert_eq!(expected, va.vpn2(), "{va:?}");
    }

    #[test]
    fn test_offset() {
        assert_offset(0x000, VA(0x0000));
        assert_offset(0x100, VA(0x0100));
        assert_offset(0xfff, VA(0x0fff));
        assert_offset(0xfff, VA(0xffff_ffff_ffff_ffff));
    }

    fn assert_offset(expected: usize, va: VA) {
        assert_eq!(expected, va.offset(), "{va:?}");
    }
}
