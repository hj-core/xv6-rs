use core::arch::asm;

pub const MAX_CPUS: usize = 8;
pub const STACK_SIZE_PER_CPU: usize = 4096;

pub fn store_mhartid_to_tp() {
    unsafe { asm!("csrr tp, mhartid") }
}

pub fn set_mstatus_to_s_mode() {
    const MSTATUS_MPP_MASK: u64 = 3 << 11; // bit mask for mode bits
    const MSTATUS_MPP_S: u64 = 1 << 11; // bits representing supervisor mode

    let mut status = read_mstatus();
    status &= !MSTATUS_MPP_MASK;
    status |= MSTATUS_MPP_S;
    write_mstatus(status);
}

fn read_mstatus() -> u64 {
    let mut result: u64;
    unsafe {
        asm!("csrr {0}, mstatus", out(reg) result);
    }
    result
}

fn write_mstatus(value: u64) {
    unsafe { asm!("csrw mstatus, {0}", in(reg) value) }
}

// Write machine exception program counter
pub fn write_mepc(value: u64) {
    unsafe { asm!("csrw mepc, {0}", in(reg) value) }
}
