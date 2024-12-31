pub mod plic;
pub mod riscv64;
pub mod uart;

pub const MAX_CPUS: usize = 8;
pub const DRAM_START: u64 = 0x8000_0000;
pub const DRAM_SIZE_IN_MB: usize = 128;
