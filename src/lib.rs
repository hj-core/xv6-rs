#![cfg_attr(not(target_arch = "riscv64"), allow(dead_code), allow(unused_imports))]
#![no_std]

pub mod kernel;
pub mod machine;
