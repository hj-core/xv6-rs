// Ref:
// Rust Atomics and Locks by Mara Bos, Chapter 4
// https://marabos.nl/atomics/building-spinlock.html

use core::cell::UnsafeCell;
use core::hint;
use core::ops::{Deref, DerefMut};
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

pub struct GuardLock<T> {
    lock: Spinlock,
    data: UnsafeCell<T>,
}

unsafe impl<T> Sync for GuardLock<T> where T: Send {}

impl<T> GuardLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            lock: Spinlock::new(),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> Guard<T> {
        self.lock.lock();
        Guard { guard_lock: self }
    }

    // pub fn unlock(&self) {
    //     Unlock is done by dropping the very existence of Guard
    // }
}

pub struct Guard<'a, T> {
    guard_lock: &'a GuardLock<T>,
}

unsafe impl<T> Send for Guard<'_, T> where T: Send {}
unsafe impl<T> Sync for Guard<'_, T> where T: Sync {}

impl<T> Deref for Guard<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        // Safety:
        // The very existence of this Guard guarantees we've exclusively
        // locked the lock.
        unsafe { &*self.guard_lock.data.get() }
    }
}

impl<T> DerefMut for Guard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety:
        // The very existence of this Guard guarantees we've exclusively
        // locked the lock.
        unsafe { &mut *self.guard_lock.data.get() }
    }
}

impl<T> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        self.guard_lock.lock.unlock();
    }
}
