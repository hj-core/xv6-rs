use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;

#[derive(Debug)]
pub struct Pinpoint {
    pub link1: AtomicPtr<Pinpoint>,
    pub link2: AtomicPtr<Pinpoint>,
}

impl Pinpoint {
    pub const fn new() -> Self {
        Self {
            link1: AtomicPtr::new(null_mut()),
            link2: AtomicPtr::new(null_mut()),
        }
    }
}

/// This trait indicates that a type has a [Pinpoint] as its FIRST field.  
/// ReprC is required to prevent field reordering.
pub trait HasPinpoint: ReprC {
    fn pinpoint(&mut self) -> &mut Pinpoint;
}

/// A marker trait indicating that the type uses C representation.
pub trait ReprC {}
