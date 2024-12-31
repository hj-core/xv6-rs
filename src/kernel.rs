use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(target_arch = "riscv64")]
use {
    crate::machine::riscv64,
    crate::machine::riscv64::{SIE_SEIE, SIE_SSIE, SIE_STIE},
};

mod lock;
mod mem;
mod plic;
mod trap;
mod uart;

static GLOBAL_ENVIRONMENT_INITIALIZED: AtomicBool = AtomicBool::new(false);

#[cfg(target_arch = "riscv64")]
pub fn s_mode_initialize() {
    if riscv64::read_tp() == 0 {
        mem::initialize();
        plic::initialize();
        uart::initialize();
        uart::busy_print_str("Hello Xv6-rs!\n");
        GLOBAL_ENVIRONMENT_INITIALIZED.store(true, Ordering::Release)
    }

    while !GLOBAL_ENVIRONMENT_INITIALIZED.load(Ordering::Acquire) {
        core::hint::spin_loop()
    }
    trap::initialize();
    plic::configure_cpu();
    configure_interrupt_enables();
    schedule_timer_interrupt();

    loop {}
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

#[cfg(target_arch = "riscv64")]
fn enable_interrupts() {
    riscv64::write_sstatus(riscv64::read_sstatus() | riscv64::SSTATUS_SIE)
}

#[cfg(target_arch = "riscv64")]
fn disable_interrupts(hart_id: u64) {
    riscv64::write_sstatus(riscv64::read_sstatus() & !riscv64::SSTATUS_SIE);
    assert_eq!(
        hart_id,
        riscv64::read_tp(),
        "Disabled interrupts for a different cpu."
    )
}

#[cfg(target_arch = "riscv64")]
fn interrupt_enabled() -> bool {
    !interrupt_disabled()
}

#[cfg(target_arch = "riscv64")]
fn interrupt_disabled() -> bool {
    riscv64::read_sstatus() & riscv64::SSTATUS_SIE == 0
}
