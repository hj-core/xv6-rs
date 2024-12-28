#![cfg(target_arch = "riscv64")]

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

// Risc-v will disable interrupt before entering the trap
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
    // No tp as we may return to another cpu.
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
    "addi sp, sp, 256",
    // Return from the trap
    "sret"
);

#[no_mangle]
fn kernel_trap_handler() {
    let scause = riscv64::read_scause();

    if scause & riscv64::SCAUSE_INTERRUPT == 0 {
        panic!("Caught an exception.");
    } else {
        match scause {
            riscv64::SCAUSE_SSI => panic!("Caught a supervisor software interrupt."),
            riscv64::SCAUSE_STI => panic!("Caught a supervisor timer interrupt."),
            riscv64::SCAUSE_SEI => panic!("Caught a supervisor external interrupt."),
            _ => panic!("Caught a unexpected supervisor interrupt."),
        }
    }
}
