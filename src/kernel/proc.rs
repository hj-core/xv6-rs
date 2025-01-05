#![cfg(target_arch = "riscv64")]

use crate::kernel::interrupt_disabled;
use crate::machine::{riscv64, MAX_CPUS};
use core::arch::asm;
use core::mem::MaybeUninit;

// Consider using AtomicPtr if a kernel heap allocator is available.
static mut CPUS: [MaybeUninit<Cpu>; MAX_CPUS] = [const { MaybeUninit::uninit() }; MAX_CPUS];

pub fn initialize() {
    assert!(interrupt_disabled());
    let hart_id = riscv64::read_tp();
    let cpu = Cpu {
        hart_id,
        context: Context::zeros(),
    };
    unsafe { CPUS[hart_id as usize].write(cpu) };
}

pub struct Cpu {
    hart_id: u64,
    context: Context,
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

    pub fn context(&mut self) -> &mut Context {
        &mut self.context
    }
}

pub struct Context {
    ra: u64,
    sp: u64,
    // Callee-saved registers
    s0: u64,
    s1: u64,
    s2: u64,
    s3: u64,
    s4: u64,
    s5: u64,
    s6: u64,
    s7: u64,
    s8: u64,
    s9: u64,
    s10: u64,
    s11: u64,
}

impl Context {
    pub const fn new(
        ra: u64,
        sp: u64,
        s0: u64,
        s1: u64,
        s2: u64,
        s3: u64,
        s4: u64,
        s5: u64,
        s6: u64,
        s7: u64,
        s8: u64,
        s9: u64,
        s10: u64,
        s11: u64,
    ) -> Self {
        Self {
            ra,
            sp,
            s0,
            s1,
            s2,
            s3,
            s4,
            s5,
            s6,
            s7,
            s8,
            s9,
            s10,
            s11,
        }
    }

    pub fn zeros() -> Self {
        Self::new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    }

    /// Save the current context and load the supplied one.
    pub fn switch(save_to: &mut Context, load_from: &Context) {
        unsafe {
            asm!(
            // Save current context
            "sd ra, 0(a0)",
            "sd sp, 8(a0)",
            "sd s0, 16(a0)",
            "sd s1, 24(a0)",
            "sd s2, 32(a0)",
            "sd s3, 40(a0)",
            "sd s4, 48(a0)",
            "sd s5, 56(a0)",
            "sd s6, 64(a0)",
            "sd s7, 72(a0)",
            "sd s8, 80(a0)",
            "sd s9, 88(a0)",
            "sd s10, 96(a0)",
            "sd s11, 104(a0)",
            // Load the supplied context
            "ld ra, 0(a1)",
            "ld sp, 8(a1)",
            "ld s0, 16(a1)",
            "ld s1, 24(a1)",
            "ld s2, 32(a1)",
            "ld s3, 40(a1)",
            "ld s4, 48(a1)",
            "ld s5, 56(a1)",
            "ld s6, 64(a1)",
            "ld s7, 72(a1)",
            "ld s8, 80(a1)",
            "ld s9, 88(a1)",
            "ld s10, 96(a1)",
            "ld s11, 104(a1)",
            "ret",
            in("a0") save_to as *mut Context as u64,
            in("a1") load_from as *const Context as u64,
            );
        }
    }
}
