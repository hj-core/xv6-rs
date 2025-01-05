#![cfg(target_arch = "riscv64")]

use crate::kernel::interrupt_disabled;
use crate::machine::{riscv64, MAX_CPUS};
use core::mem::MaybeUninit;

// Consider using AtomicPtr if a kernel heap allocator is available.
static mut CPUS: [MaybeUninit<Cpu>; MAX_CPUS] = [const { MaybeUninit::uninit() }; MAX_CPUS];

pub fn initialize() {
    assert!(interrupt_disabled());
    let hart_id = riscv64::read_tp();
    let cpu = Cpu { hart_id };
    unsafe { CPUS[hart_id as usize].write(cpu) };
}

pub struct Cpu {
    hart_id: u64,
}

impl Cpu {
    pub fn this<'a>() -> &'a mut Self {
        assert!(interrupt_disabled());
        let hart_id = riscv64::read_tp();
        unsafe { CPUS[hart_id as usize].assume_init_mut() }
    }

    pub fn hart_id(&self) -> u64 {
        self.hart_id
    }
}
