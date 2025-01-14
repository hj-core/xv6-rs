use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;

#[derive(Debug)]
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

/// This trait indicates that a type has a hole (i.e., a [ListNode]) as its first field.  
/// The hole may be linked to other holes.
/// Besides, it can act as an anchor to get the object's starting address.
/// ReprC is required to prevent field reordering.
pub trait HasHole: ReprC {
    fn hole(&mut self) -> &mut ListNode;
}

/// A marker trait indicating that the type uses C representation.
pub trait ReprC {}
