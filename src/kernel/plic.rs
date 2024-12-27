#![cfg(target_arch = "riscv64")]

use crate::machine::{plic, riscv64};
use plic::VIRT_UART0_SOURCE_NUMBER;

pub fn initialize() {
    plic::set_priority(VIRT_UART0_SOURCE_NUMBER, 1);
}

pub fn configure_cpu() {
    let context = context(riscv64::read_tp() as u32);
    plic::enable_interrupt(context, VIRT_UART0_SOURCE_NUMBER);
    plic::set_priority_threshold(context, 0);
}

// Learned from the xv6-riscv repository.
// This setting may exist in the hw/riscv/virt.c of qemu repository.
fn context(hart_id: u32) -> u32 {
    1 + hart_id * 2
}
