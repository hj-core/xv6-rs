use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;

pub struct ListNode {
    pub prev: AtomicPtr<ListNode>,
    pub next: AtomicPtr<ListNode>,
}

impl ListNode {
    pub const fn new() -> Self {
        Self {
            prev: AtomicPtr::new(null_mut()),
            next: AtomicPtr::new(null_mut()),
        }
    }
}
