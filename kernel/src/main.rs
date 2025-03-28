#![cfg(target_arch = "riscv64")]
#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;
use hw::riscv64::{MCOUNTEREN_TM, MENVCFG_STCE, MIE_STIE, MSTATUS_MPP_MASK, MSTATUS_MPP_S};
use hw::{riscv64, MAX_CPUS};
use wrapper::Bytes;

// Entry point.
// Must be placed at the address where qemu's -kernel jumps.
// It just calls the _start.
global_asm!(
    ".section .text.entry.must_at_0x8000_0000",
    ".global _entry",
    "_entry:",
    "call _start"
);

const STACK_SIZE_PER_CPU: Bytes = Bytes(4096);

#[repr(C, align(16))]
struct CpuStacks([u8; STACK_SIZE_PER_CPU.0 * MAX_CPUS]);

static CPU_STACKS: CpuStacks = CpuStacks([0; STACK_SIZE_PER_CPU.0 * MAX_CPUS]);

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    unsafe {
        asm!(
        // Set up stack for each CPU.
        "csrr a2, mhartid",
        "addi a2, a2, 1",
        "mul a2, a2, a1",
        "add sp, a0, a2",
        // Jump to m_mode_initialize
        "call m_mode_initialize",
        in("a0") &raw const CPU_STACKS.0,
        in("a1") STACK_SIZE_PER_CPU.0,
        );
    }
    loop {}
}

#[unsafe(no_mangle)]
fn m_mode_initialize() {
    store_mhartid_to_tp();
    allow_s_mode_manage_all_physical_memories();
    delegate_exceptions_to_s_mode();
    delegate_interrupts_to_s_mode();
    configure_timer_interrupt();
    set_return_mode_to_s_mode();
    set_mepc_to_s_mode_initialize();
    jump_to_s_mode();
}

fn store_mhartid_to_tp() {
    unsafe { asm!("csrr tp, mhartid") }
}

fn allow_s_mode_manage_all_physical_memories() {
    riscv64::write_pmpaddr0(0x3f_ffff_ffff_ffff);
    riscv64::write_pmpcfg0(0xf);
}

fn delegate_exceptions_to_s_mode() {
    // Some bits are read-only zero so the resulting medeleg is not 0xffff
    riscv64::write_medeleg(0xffff)
}

fn delegate_interrupts_to_s_mode() {
    // Some bits are read-only zero so the resulting mideleg is not 0xffff
    riscv64::write_mideleg(0xffff)
}

fn configure_timer_interrupt() {
    // Enable S-mode timer interrupt
    riscv64::write_mie(riscv64::read_mie() | MIE_STIE);

    // Enable the "Sstc" extension for S-mode timer interrupt, i.e., stimecmp
    riscv64::write_menvcfg(riscv64::read_menvcfg() | MENVCFG_STCE);

    // Allow S-mode to read time
    riscv64::write_mcounteren(riscv64::read_mcounteren() | MCOUNTEREN_TM);
}

fn set_return_mode_to_s_mode() {
    let mut status = riscv64::read_mstatus();
    status &= !MSTATUS_MPP_MASK;
    status |= MSTATUS_MPP_S;
    riscv64::write_mstatus(status);
}

fn set_mepc_to_s_mode_initialize() {
    riscv64::write_mepc(kernel::s_mode_initialize as *const () as u64);
}

fn jump_to_s_mode() {
    unsafe { asm!("mret") }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
