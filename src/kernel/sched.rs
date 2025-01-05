#![cfg(target_arch = "riscv64")]

use crate::kernel;
use crate::kernel::proc::Cpu;
use crate::kernel::uart;
use crate::machine::riscv64;

pub fn start() {
    assert!(kernel::interrupt_disabled());
    let cpu = Cpu::this();
    assert_eq!(riscv64::read_tp(), cpu.hart_id());

    uart::busy_print_str("hart ");
    uart::busy_print_byte(cpu.hart_id().to_le_bytes()[0] + 48);
    uart::busy_print_str(" reported duty.\n");

    loop {}
}
