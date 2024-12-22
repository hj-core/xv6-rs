pub mod riscv64;
pub mod uart;

use core::arch::asm;

pub const MAX_CPUS: usize = 8;
