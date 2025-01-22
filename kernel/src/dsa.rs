use core::marker::PhantomPinned;
use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;

/// This struct is intended to be used as a field within address-sensitive struct.
///
/// # CAUTION:
/// 
/// repr(C) seems not working. 
/// The link2 comes before link1 in the initialized FREE_PAGE.
/// 
/// todo!("why?")
#[derive(Debug)]
#[repr(C)]
pub struct Pinpoint {
    pub link1: AtomicPtr<Pinpoint>,
    pub link2: AtomicPtr<Pinpoint>,
    _pinned: PhantomPinned,
}

impl Pinpoint {
    pub const fn new() -> Self {
        Self {
            link1: AtomicPtr::new(null_mut()),
            link2: AtomicPtr::new(null_mut()),
            _pinned: PhantomPinned,
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
