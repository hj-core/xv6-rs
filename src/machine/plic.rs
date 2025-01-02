// Ref:
// RISC-V Platform-Level Interrupt Controller Specification
// https://github.com/riscv/riscv-plic-spec/blob/master/riscv-plic.adoc

use crate::wrapper::{Address, Bytes};

// The memory map address of PLIC
const PLIC_BASE: Address = Address(0xc00_0000);

const MAX_SOURCES: u32 = 1024;
const MAX_CONTEXTS: u32 = 15872;

// Source:
// https://github.com/qemu/qemu/blob/master/include/hw/riscv/virt.h#L92
pub const VIRT_UART0_SOURCE_NUMBER: u32 = 10;

pub fn set_priority(source_no: u32, priority: u32) {
    check_source_number(source_no);
    let addr_ptr: *mut u32 = priority_addr(source_no).into();
    unsafe { addr_ptr.write_volatile(priority) }
}

fn check_source_number(value: u32) {
    assert!(
        0 < value && value < MAX_SOURCES,
        "Source {value} does not exist.",
    );
}

fn priority_addr(source_no: u32) -> Address {
    let count = source_no << 2;
    PLIC_BASE + Bytes(count as usize)
}

pub fn enable_interrupt(context_no: u32, source_no: u32) {
    check_context_number(context_no);
    check_source_number(source_no);
    let addr_ptr: *mut u32 = interrupt_enable_addr(context_no, source_no).into();
    unsafe {
        let old_value = addr_ptr.read_volatile();
        let new_value = old_value | interrupt_enable_bit(source_no);
        addr_ptr.write_volatile(new_value);
    }
}

fn check_context_number(value: u32) {
    assert!(value < MAX_CONTEXTS, "Context {value} does not exist.");
}

fn interrupt_enable_addr(context_no: u32, source_no: u32) -> Address {
    let count = 0x00_2000 + (context_no << 7) + ((source_no >> 5) << 2);
    PLIC_BASE + Bytes(count as usize)
}

fn interrupt_enable_bit(source_no: u32) -> u32 {
    1 << (source_no & 0x1f)
}

pub fn set_priority_threshold(context_no: u32, threshold: u32) {
    check_context_number(context_no);
    let addr_ptr: *mut u32 = priority_threshold_addr(context_no).into();
    unsafe { addr_ptr.write_volatile(threshold) }
}

fn priority_threshold_addr(context_no: u32) -> Address {
    let count = 0x20_0000 + (context_no << 12);
    PLIC_BASE + Bytes(count as usize)
}

pub fn claim_interrupt(context_no: u32) -> u32 {
    check_context_number(context_no);
    let addr_ptr: *const u32 = claim_complete_addr(context_no).into();
    unsafe { addr_ptr.read_volatile() }
}

fn claim_complete_addr(context_no: u32) -> Address {
    let count = 0x20_0004 + (context_no << 12);
    PLIC_BASE + Bytes(count as usize)
}

pub fn complete_interrupt(context_no: u32, source_no: u32) {
    check_context_number(context_no);
    check_source_number(source_no);
    let addr_ptr: *mut u32 = claim_complete_addr(context_no).into();
    unsafe { addr_ptr.write_volatile(source_no) }
}

#[cfg(test)]
mod tests {
    use super::{
        claim_complete_addr, interrupt_enable_addr, interrupt_enable_bit, priority_addr,
        priority_threshold_addr, PLIC_BASE as BASE,
    };
    use crate::wrapper::{Address, Bytes};

    #[test]
    fn test_priority_addr() {
        assert_priority_addr(BASE + Bytes(0x000004), 1);
        assert_priority_addr(BASE + Bytes(0x000008), 2);
        assert_priority_addr(BASE + Bytes(0x000FFC), 1023);
    }

    fn assert_priority_addr(expect: Address, source_no: u32) {
        let actual = priority_addr(source_no);
        assert_eq!(expect, actual, "source_no={source_no}");
    }

    #[test]
    fn test_interrupt_enable_addr() {
        assert_interrupt_enable_addr(BASE + Bytes(0x002000), 0, 0);
        assert_interrupt_enable_addr(BASE + Bytes(0x002000), 0, 31);
        assert_interrupt_enable_addr(BASE + Bytes(0x002004), 0, 32);
        assert_interrupt_enable_addr(BASE + Bytes(0x002084), 1, 48);
        assert_interrupt_enable_addr(BASE + Bytes(0x002100), 2, 0);
        assert_interrupt_enable_addr(BASE + Bytes(0x00217C), 2, 1023);
        assert_interrupt_enable_addr(BASE + Bytes(0x1F1F84), 15871, 60);
        assert_interrupt_enable_addr(BASE + Bytes(0x1F1FFC), 15871, 1023);
    }

    fn assert_interrupt_enable_addr(expect: Address, context_no: u32, source_no: u32) {
        let actual = interrupt_enable_addr(context_no, source_no);
        assert_eq!(
            expect, actual,
            "context_no={context_no}, source_no={source_no}"
        );
    }

    #[test]
    fn test_interrupt_enable_bit() {
        assert_interrupt_enable_bit(1 << 0, 0);
        assert_interrupt_enable_bit(1 << 15, 15);
        assert_interrupt_enable_bit(1 << 31, 31);
        assert_interrupt_enable_bit(1 << 0, 32);
        assert_interrupt_enable_bit(1 << 20, 52);
        assert_interrupt_enable_bit(1 << 31, 63);
        assert_interrupt_enable_bit(1 << 0, 992);
        assert_interrupt_enable_bit(1 << 8, 1000);
        assert_interrupt_enable_bit(1 << 31, 1023);
    }

    fn assert_interrupt_enable_bit(expect: u32, source_no: u32) {
        let actual = interrupt_enable_bit(source_no);
        assert_eq!(expect, actual, "source_no={source_no}");
    }

    #[test]
    fn test_priority_threshold_addr() {
        assert_priority_threshold_addr(BASE + Bytes(0x200000), 0);
        assert_priority_threshold_addr(BASE + Bytes(0x201000), 1);
        assert_priority_threshold_addr(BASE + Bytes(0x203000), 3);
        assert_priority_threshold_addr(BASE + Bytes(0x3FFF000), 15871);
    }

    fn assert_priority_threshold_addr(expected: Address, context_no: u32) {
        let actual = priority_threshold_addr(context_no);
        assert_eq!(expected, actual, "context_no={context_no}");
    }

    #[test]
    fn test_claim_complete_addr() {
        assert_claim_complete_addr(BASE + Bytes(0x200004), 0);
        assert_claim_complete_addr(BASE + Bytes(0x201004), 1);
        assert_claim_complete_addr(BASE + Bytes(0x203004), 3);
        assert_claim_complete_addr(BASE + Bytes(0x3FFF004), 15871);
    }

    fn assert_claim_complete_addr(expected: Address, context_no: u32) {
        let actual = claim_complete_addr(context_no);
        assert_eq!(expected, actual, "context_no={context_no}");
    }
}
