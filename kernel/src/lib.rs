#![cfg_attr(not(target_arch = "riscv64"), allow(dead_code), allow(unused_imports))]
#![no_std]
#![allow(dead_code)]

mod dsa;
mod lock;
mod mem;
mod plic;
mod proc;
mod sched;
mod trap;
mod uart;

use crate::dsa::ListNode;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(target_arch = "riscv64")]
use {
    hw::riscv64,
    hw::riscv64::{SIE_SEIE, SIE_SSIE, SIE_STIE},
};

static GLOBAL_ENVIRONMENT_INITIALIZED: AtomicBool = AtomicBool::new(false);

#[cfg(target_arch = "riscv64")]
pub fn s_mode_initialize() {
    if riscv64::read_tp() == 0 {
        uart::initialize();
        uart::busy_print_str("Hello xv6-rs!\n");
        plic::initialize();
        mem::initialize();
        mem::virt::initialize();
        GLOBAL_ENVIRONMENT_INITIALIZED.store(true, Ordering::Release)
    }

    while !GLOBAL_ENVIRONMENT_INITIALIZED.load(Ordering::Acquire) {
        core::hint::spin_loop()
    }
    trap::initialize();
    plic::configure_cpu();
    configure_interrupt_enables();
    schedule_timer_interrupt();
    mem::virt::configure_cpu();
    proc::initialize();
    sched::start();
}

#[cfg(target_arch = "riscv64")]
fn configure_interrupt_enables() {
    // Configure the types of interrupts to receive
    riscv64::write_sie(riscv64::read_sie() | SIE_SEIE | SIE_STIE | SIE_SSIE);
}

#[cfg(target_arch = "riscv64")]
fn schedule_timer_interrupt() {
    // Schedule the next timer interrupt
    riscv64::write_stimecmp(riscv64::read_time() + TIMER_INTERRUPT_INTERVAL.0)
}

const TIMER_INTERRUPT_INTERVAL: Ticks = Ticks(1_000_000);

struct Ticks(u64);

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

/// This trait indicates that a type has a hole (i.e., a [ListNode]) as its first field.  
/// The hole may be linked to other holes.
/// Besides, it can act as an anchor to get the object's starting address.
trait HasHole {
    fn hole(&mut self) -> &mut ListNode;
}

/// A marker trait indicating that the type uses C representation.
trait ReprC {}
