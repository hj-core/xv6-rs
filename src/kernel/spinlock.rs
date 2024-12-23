// Ref:
// Rust Atomics and Locks by Mara Bos, Chapter 4
// https://marabos.nl/atomics/building-spinlock.html

use core::hint;
use core::sync::atomic::{AtomicBool, Ordering};

pub struct Spinlock {
    locked: AtomicBool,
}

impl Spinlock {
    pub const fn new() -> Self {
        Self {
            locked: AtomicBool::new(false),
        }
    }

    pub fn lock(&self) {
        while self.locked.swap(true, Ordering::Acquire) {
            hint::spin_loop();
        }
    }

    pub fn unlock(&self) {
        self.locked.store(false, Ordering::Release);
    }
}
