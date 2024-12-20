#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;
use xv6_rs::kernel;
use xv6_rs::machine;

// Entry point.
// Must be placed at the address where qemu's -kernel jumps.
// It just calls the _start.
global_asm!(".section .text", ".global _entry", "_entry:", "call _start");

#[repr(C, align(16))]
struct CpuStack {
    data: [u8; machine::STACK_SIZE_PER_CPU * machine::MAX_CPUS],
}

static CPU_STACK: CpuStack = CpuStack {
    data: [0; machine::STACK_SIZE_PER_CPU * machine::MAX_CPUS],
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
        in("a1") machine::STACK_SIZE_PER_CPU,
        );
    }
    loop {}
}

#[no_mangle]
fn start_cpu() {
    machine::store_mhartid_to_tp();
    machine::set_mstatus_to_s_mode();
    machine::write_mepc(kernel::main as *const () as u64);
    machine::disable_paging();
    machine::delegate_exceptions_to_s_mode();
    machine::delegate_interrupts_to_s_mode();
    machine::enable_s_mode_interrupts();
    machine::allow_s_mode_read_all_physical_memories();
    machine::set_up_timer_interrupts();
    machine::store_mhartid_to_tp();
    // Switch to supervisor mode and jump to kernel::main
    unsafe { asm!("mret") }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
