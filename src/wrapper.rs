use core::ops::{Add, Mul};

#[derive(Copy, Clone)]
pub struct Bytes(pub usize);

impl Add<Bytes> for Bytes {
    type Output = Self;

    fn add(self, rhs: Bytes) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Mul<usize> for Bytes {
    type Output = Self;
    fn mul(self, rhs: usize) -> Self::Output {
        Bytes(self.0 * rhs)
    }
}

impl From<MiB> for Bytes {
    fn from(value: MiB) -> Self {
        Self(value.0 << 20)
    }
}

#[derive(Copy, Clone)]
pub struct MiB(pub usize);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Address(pub u64);

impl Add<Bytes> for Address {
    type Output = Self;

    fn add(self, rhs: Bytes) -> Self::Output {
        Self(self.0 + rhs.0 as u64)
    }
}

impl<T> Into<*const T> for Address {
    fn into(self) -> *const T {
        self.0 as *const T
    }
}

impl<T> Into<*mut T> for Address {
    fn into(self) -> *mut T {
        self.0 as *mut T
    }
}

impl<T> From<*const T> for Address {
    fn from(ptr: *const T) -> Self {
        Self(ptr as u64)
    }
}
