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

pub fn disable_paging() {
    write_satp(0)
}

// Write supervisor address translation and protection
fn write_satp(value: u64) {
    unsafe { asm!("csrw satp, {0}", in(reg) value) }
}

pub fn delegate_exceptions_to_s_mode() {
    // Some bits are read-only zero so the resulting medeleg is not 0xffff
    write_medeleg(0xffff)
}

// Write machine exception delegation
fn write_medeleg(value: u64) {
    unsafe { asm!("csrw medeleg, {0}", in(reg) value) }
}

pub fn delegate_interrupts_to_s_mode() {
    // Some bits are read-only zero so the resulting mideleg is not 0xffff
    write_mideleg(0xffff)
}

// Write machine interrupt delegation
fn write_mideleg(value: u64) {
    unsafe { asm!("csrw mideleg, {0}", in(reg) value) }
}

pub fn enable_s_mode_interrupts() {
    const SIE_SEIE: u64 = 1 << 9; // External interrupts
    const SIE_STIE: u64 = 1 << 5; // Timer interrupts
    const SIE_SSIE: u64 = 1 << 1; // Software interrupts

    write_sie(read_sie() | SIE_SEIE | SIE_STIE | SIE_SSIE);
}

// Write supervisor interrupt enable
fn write_sie(value: u64) {
    unsafe { asm!("csrw sie, {0}", in(reg) value) }
}

fn read_sie() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, sie", out(reg) result) };
    result
}

pub fn allow_s_mode_read_all_physical_memories() {
    write_pmpaddr0(0x3fffffffffffff);
    write_pmpcfg0(0xf);
}

// Write physical memory protection address 0
fn write_pmpaddr0(value: u64) {
    unsafe { asm!("csrw pmpaddr0, {0}", in(reg) value) }
}

// Write physical memory protection configuration 0
fn write_pmpcfg0(value: u64) {
    unsafe { asm!("csrw pmpcfg0, {0}", in(reg) value) }
}

pub fn set_up_timer_interrupts() {
    // Enable S-mode timer interrupts in mie
    const MIE_STIE: u64 = 1 << 5;
    write_mie(read_mie() | MIE_STIE);

    // Enable the "Sstc" extension for S-mode timer interrupts, i.e., stimecmp
    const MENVCFG_STCE: u64 = 1 << 63;
    write_menvcfg(read_menvcfg() | MENVCFG_STCE);

    // Allow S-mode to read time
    const MCOUNTEREN_TM: u64 = 0x2;
    write_mcounteren(read_mcounteren() | MCOUNTEREN_TM);

    // Ask for the very first timer interrupt
    write_stimecmp(read_time() + 1_000_000)
}

// Write machine interrupt enable
fn write_mie(value: u64) {
    unsafe { asm!("csrw mie, {0}", in(reg) value) }
}

fn read_mie() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mie", out(reg) result) };
    result
}

// Write machine environment configuration
fn write_menvcfg(value: u64) {
    unsafe { asm!("csrw menvcfg, {0}", in(reg) value) }
}

fn read_menvcfg() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, menvcfg", out(reg) result) };
    result
}

// Write machine counter-enable
fn write_mcounteren(value: u64) {
    unsafe { asm!("csrw mcounteren, {0}", in(reg) value) }
}

fn read_mcounteren() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, mcounteren", out(reg) result) };
    result
}

// Write supervisor timer
fn write_stimecmp(value: u64) {
    unsafe { asm!("csrw stimecmp, {0}", in(reg) value) }
}

// Read machine(?) timer
fn read_time() -> u64 {
    let mut result: u64;
    unsafe { asm!("csrr {0}, time", out(reg) result) };
    result
}
