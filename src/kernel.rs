#[cfg(target_arch = "riscv64")]
use {
    crate::machine::riscv64,
    crate::machine::riscv64::{SIE_SEIE, SIE_SSIE, SIE_STIE},
};

mod spinlock;
mod trap;
mod uart;

#[cfg(target_arch = "riscv64")]
pub fn s_mode_initialize() {
    configure_interrupt_enables();
    schedule_timer_interrupt();
    trap::initialize();
    uart::initialize();
    // Issue an illegal instruction
    riscv64::read_mstatus();
    uart::busy_print("Hello World!\n");
}

#[cfg(target_arch = "riscv64")]
fn configure_interrupt_enables() {
    // Configure the types of interrupts to receive
    riscv64::write_sie(riscv64::read_sie() | SIE_SEIE | SIE_STIE | SIE_SSIE);
}

#[cfg(target_arch = "riscv64")]
fn schedule_timer_interrupt() {
    // Ask for the very first timer interrupt
    riscv64::write_stimecmp(riscv64::read_time() + TIMER_INTERRUPT_INTERVAL)
}

const TIMER_INTERRUPT_INTERVAL: u64 = 1_000_000; // Tenth of a second
