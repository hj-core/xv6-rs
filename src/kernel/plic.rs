#![cfg(target_arch = "riscv64")]

use crate::machine::{plic, riscv64};
use plic::UART0_SOURCE_NUMBER;

pub fn initialize() {
    plic::set_priority(UART0_SOURCE_NUMBER, 1);
}

pub fn configure_cpu() {
    let context_no = context_no(riscv64::read_tp());
    plic::enable_interrupt(context_no, UART0_SOURCE_NUMBER);
    plic::set_priority_threshold(context_no, 0);
}

// Learned from the xv6-riscv repository.
// Possible relevant information in hw/riscv/virt.c.
fn context_no(hart_id: u64) -> u32 {
    1 + (hart_id as u32) * 2
}
