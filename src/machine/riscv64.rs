#![cfg(target_arch = "riscv64")]

use core::arch::asm;

pub fn write_mstatus(value: u64) {
    unsafe { asm!("csrw mstatus, {0}", in(reg) value) }
}

pub fn read_mstatus() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mstatus", out(reg) result) }
    result
}

/// Write machine exception program counter
pub fn write_mepc(value: u64) {
    unsafe { asm!("csrw mepc, {0}", in(reg) value) }
}

/// Write supervisor address translation and protection
pub fn write_satp(value: u64) {
    unsafe { asm!("csrw satp, {0}", in(reg) value) }
}

/// Write machine exception delegation
pub fn write_medeleg(value: u64) {
    unsafe { asm!("csrw medeleg, {0}", in(reg) value) }
}

/// Write machine interrupt delegation
pub fn write_mideleg(value: u64) {
    unsafe { asm!("csrw mideleg, {0}", in(reg) value) }
}

/// Write supervisor interrupt enable
pub fn write_sie(value: u64) {
    unsafe { asm!("csrw sie, {0}", in(reg) value) }
}

pub fn read_sie() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, sie", out(reg) result) };
    result
}

/// Write physical memory protection address 0
pub fn write_pmpaddr0(value: u64) {
    unsafe { asm!("csrw pmpaddr0, {0}", in(reg) value) }
}

/// Write physical memory protection configuration 0
pub fn write_pmpcfg0(value: u64) {
    unsafe { asm!("csrw pmpcfg0, {0}", in(reg) value) }
}

/// Write machine interrupt enable
pub fn write_mie(value: u64) {
    unsafe { asm!("csrw mie, {0}", in(reg) value) }
}

pub fn read_mie() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mie", out(reg) result) };
    result
}

/// Write machine environment configuration
pub fn write_menvcfg(value: u64) {
    unsafe { asm!("csrw menvcfg, {0}", in(reg) value) }
}

pub fn read_menvcfg() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, menvcfg", out(reg) result) };
    result
}

/// Write machine counter-enable
pub fn write_mcounteren(value: u64) {
    unsafe { asm!("csrw mcounteren, {0}", in(reg) value) }
}

pub fn read_mcounteren() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mcounteren", out(reg) result) };
    result
}

/// Write supervisor timer
pub fn write_stimecmp(value: u64) {
    unsafe { asm!("csrw stimecmp, {0}", in(reg) value) }
}

/// Read machine(?) timer
pub fn read_time() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, time", out(reg) result) };
    result
}
