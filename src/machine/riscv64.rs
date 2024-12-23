use core::arch::asm;

pub fn write_mstatus(value: u64) {
    unsafe { asm!("csrw mstatus, {0}", in(reg) value) }
}

pub fn read_mstatus() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mstatus", out(reg) result) }
    result
}

pub const MSTATUS_MPP_MASK: u64 = 3 << 11; // bit mask for mode bits
pub const MSTATUS_MPP_S: u64 = 1 << 11; // bits representing supervisor mode

/// Write machine exception program counter
pub fn write_mepc(value: u64) {
    unsafe { asm!("csrw mepc, {0}", in(reg) value) }
}

/// Write machine exception delegation
pub fn write_medeleg(value: u64) {
    unsafe { asm!("csrw medeleg, {0}", in(reg) value) }
}

/// Write machine interrupt delegation
pub fn write_mideleg(value: u64) {
    unsafe { asm!("csrw mideleg, {0}", in(reg) value) }
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

pub const MIE_STIE: u64 = 1 << 5;

/// Write machine environment configuration
pub fn write_menvcfg(value: u64) {
    unsafe { asm!("csrw menvcfg, {0}", in(reg) value) }
}

pub fn read_menvcfg() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, menvcfg", out(reg) result) };
    result
}

pub const MENVCFG_STCE: u64 = 1 << 63;

/// Write machine counter-enable
pub fn write_mcounteren(value: u64) {
    unsafe { asm!("csrw mcounteren, {0}", in(reg) value) }
}

pub fn read_mcounteren() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mcounteren", out(reg) result) };
    result
}

pub const MCOUNTEREN_TM: u64 = 0x2;

/// Write supervisor address translation and protection
pub fn write_satp(value: u64) {
    unsafe { asm!("csrw satp, {0}", in(reg) value) }
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

pub const SIE_SEIE: u64 = 1 << 9; // External interrupts
pub const SIE_STIE: u64 = 1 << 5; // Timer interrupts
pub const SIE_SSIE: u64 = 1 << 1; // Software interrupts

/// Write supervisor timer
pub fn write_stimecmp(value: u64) {
    unsafe { asm!("csrw stimecmp, {0}", in(reg) value) }
}

/// Read real-time counter
pub fn read_time() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, time", out(reg) result) };
    result
}
