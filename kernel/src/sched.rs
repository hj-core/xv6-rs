#![cfg(target_arch = "riscv64")]

use crate::proc::{Context, Cpu};
use crate::{interrupt_disabled, uart};
use hw::riscv64;

pub fn start() {
    assert!(interrupt_disabled());
    let cpu = Cpu::this();
    let hart_id = riscv64::read_tp();
    assert_eq!(hart_id, cpu.hart_id());

    uart::busy_print_str("hart ");
    uart::busy_print_byte(cpu.hart_id().to_le_bytes()[0] + 48);
    uart::busy_print_str(" reported duty.\n");

    let context = Context::new(
        0x8001_0000 + hart_id * 0x1_0000 + 0x100,
        0x8001_0000 + hart_id * 0x1_0000 + 0x200,
        0x8001_0000 + hart_id * 0x1_0000 + 0x300,
        0x8001_0000 + hart_id * 0x1_0000 + 0x310,
        0x8001_0000 + hart_id * 0x1_0000 + 0x320,
        0x8001_0000 + hart_id * 0x1_0000 + 0x330,
        0x8001_0000 + hart_id * 0x1_0000 + 0x340,
        0x8001_0000 + hart_id * 0x1_0000 + 0x350,
        0x8001_0000 + hart_id * 0x1_0000 + 0x360,
        0x8001_0000 + hart_id * 0x1_0000 + 0x370,
        0x8001_0000 + hart_id * 0x1_0000 + 0x380,
        0x8001_0000 + hart_id * 0x1_0000 + 0x390,
        0x8001_0000 + hart_id * 0x1_0000 + 0x3a0,
        0x8001_0000 + hart_id * 0x1_0000 + 0x3b0,
    );
    Context::switch(cpu.context(), &context);
    loop {}
}
