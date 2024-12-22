#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;
use xv6_rs::machine::riscv64;
use xv6_rs::{kernel, machine};

// Entry point.
// Must be placed at the address where qemu's -kernel jumps.
// It just calls the _start.
global_asm!(".section .text", ".global _entry", "_entry:", "call _start");

const STACK_SIZE_PER_CPU: usize = 4096;

#[repr(C, align(16))]
struct CpuStack {
    data: [u8; STACK_SIZE_PER_CPU * machine::MAX_CPUS],
}

static CPU_STACK: CpuStack = CpuStack {
    data: [0; STACK_SIZE_PER_CPU * machine::MAX_CPUS],
};

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe {
        asm!(
        // set up stack for each CPU.
        "csrr a2, mhartid",
        "addi a2, a2, 1",
        "mul a2, a2, a1",
        "add sp, a0, a2",
        // jump to start_cpu
        "call start_cpu",
        in("a0") &raw const CPU_STACK.data,
        in("a1") STACK_SIZE_PER_CPU,
        );
    }
    loop {}
}

#[no_mangle]
fn start_cpu() {
    store_mhartid_to_tp();
    change_mstatus_to_s_mode();
    change_mepc_to_kernel_main();
    disable_paging();
    allow_s_mode_manage_all_physical_memories();
    delegate_exceptions_to_s_mode();
    delegate_interrupts_to_s_mode();
    enable_s_mode_interrupts();
    configure_timer_interrupt();
    leave_machine_mode(); // Jump to kernel::main in S-mode
}

fn store_mhartid_to_tp() {
    unsafe { asm!("csrr tp, mhartid") }
}

fn change_mstatus_to_s_mode() {
    const MSTATUS_MPP_MASK: u64 = 3 << 11; // bit mask for mode bits
    const MSTATUS_MPP_S: u64 = 1 << 11; // bits representing supervisor mode
    let mut status = riscv64::read_mstatus();
    status &= !MSTATUS_MPP_MASK;
    status |= MSTATUS_MPP_S;
    riscv64::write_mstatus(status);
}

fn change_mepc_to_kernel_main() {
    riscv64::write_mepc(kernel::main as *const () as u64);
}

fn disable_paging() {
    riscv64::write_satp(0)
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

fn enable_s_mode_interrupts() {
    const SIE_SEIE: u64 = 1 << 9; // External interrupts
    const SIE_STIE: u64 = 1 << 5; // Timer interrupts
    const SIE_SSIE: u64 = 1 << 1; // Software interrupts
    riscv64::write_sie(riscv64::read_sie() | SIE_SEIE | SIE_STIE | SIE_SSIE);
}

fn configure_timer_interrupt() {
    // Enable S-mode timer interrupts in mie
    const MIE_STIE: u64 = 1 << 5;
    riscv64::write_mie(riscv64::read_mie() | MIE_STIE);

    // Enable the "Sstc" extension for S-mode timer interrupts, i.e., stimecmp
    const MENVCFG_STCE: u64 = 1 << 63;
    riscv64::write_menvcfg(riscv64::read_menvcfg() | MENVCFG_STCE);

    // Allow S-mode to read time
    const MCOUNTEREN_TM: u64 = 0x2;
    riscv64::write_mcounteren(riscv64::read_mcounteren() | MCOUNTEREN_TM);

    // Ask for the very first timer interrupt
    riscv64::write_stimecmp(riscv64::read_time() + 1_000_000)
}

fn leave_machine_mode() {
    unsafe { asm!("mret") }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
