use core::sync::atomic::AtomicPtr;

pub struct ListNode {
    pub prev: AtomicPtr<ListNode>,
    pub next: AtomicPtr<ListNode>,
}
