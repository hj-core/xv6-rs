#![no_std]

pub mod plic;
pub mod riscv64;
pub mod uart;

use wrapper::{Address, Bytes};

pub const WORD_SIZE: Bytes = Bytes(8);
pub const MAX_CPUS: usize = 8;
pub const DRAM_START: Address = Address(0x8000_0000);
pub const DRAM_SIZE: Bytes = Bytes(128 << 20);
