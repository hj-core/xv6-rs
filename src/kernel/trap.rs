#![cfg(target_arch = "riscv64")]

use crate::kernel::uart;
use crate::machine::riscv64;
use core::arch::global_asm;

pub fn initialize() {
    install_kernel_trap_vec();
}

fn install_kernel_trap_vec() {
    riscv64::write_stvec(kernel_trap_vec as *const u64 as u64);
}

extern "C" {
    fn kernel_trap_vec();
}

global_asm!(
    ".global kernel_trap_vec",
    ".align 4", // implicit set the stvec to direct mode
    "kernel_trap_vec:",
    // Save caller-saved registers
    "addi sp, sp, -256",
    "sd ra, 0(sp)",
    "sd sp, 8(sp)",
    "sd gp, 16(sp)",
    "sd tp, 24(sp)",
    "sd t0, 32(sp)",
    "sd t1, 40(sp)",
    "sd t2, 48(sp)",
    "sd a0, 72(sp)",
    "sd a1, 80(sp)",
    "sd a2, 88(sp)",
    "sd a3, 96(sp)",
    "sd a4, 104(sp)",
    "sd a5, 112(sp)",
    "sd a6, 120(sp)",
    "sd a7, 128(sp)",
    "sd t3, 216(sp)",
    "sd t4, 224(sp)",
    "sd t5, 232(sp)",
    "sd t6, 240(sp)",
    // Call trap handler
    "call kernel_trap_handler",
    // Restore caller-saved registers.
    // Not including tp as we may have moved to another cpu.
    "ld ra, 0(sp)",
    "ld sp, 8(sp)",
    "ld gp, 16(sp)",
    "ld t0, 32(sp)",
    "ld t1, 40(sp)",
    "ld t2, 48(sp)",
    "ld a0, 72(sp)",
    "ld a1, 80(sp)",
    "ld a2, 88(sp)",
    "ld a3, 96(sp)",
    "ld a4, 104(sp)",
    "ld a5, 112(sp)",
    "ld a6, 120(sp)",
    "ld a7, 128(sp)",
    "ld t3, 216(sp)",
    "ld t4, 224(sp)",
    "ld t5, 232(sp)",
    "ld t6, 240(sp)",
    // Adjust sp and return from trap
    "addi sp, sp, 256",
    "sret"
);

#[no_mangle]
fn kernel_trap_handler() {
    uart::busy_print("Caught one!\n");
    panic!();
}
