pub mod plic;
pub mod riscv64;
pub mod uart;

use crate::wrapper::{Address, MiB};

pub const MAX_CPUS: usize = 8;
pub const DRAM_START: Address = Address(0x8000_0000);
pub const DRAM_SIZE: MiB = MiB(128);
