use core::arch::asm;

pub const MAX_CPUS: usize = 8;
pub const STACK_SIZE_PER_CPU: usize = 4096;

pub fn store_mhartid_to_tp() {
    unsafe { asm!("csrr tp, mhartid") }
}
