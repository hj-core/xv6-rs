#![no_std]

use core::ops::{Add, Mul};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Address(pub usize);

impl Add<Bytes> for Address {
    type Output = Self;

    fn add(self, rhs: Bytes) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<T> From<*const T> for Address {
    fn from(ptr: *const T) -> Self {
        Self(ptr as usize)
    }
}

impl<T> Into<*const T> for Address {
    fn into(self) -> *const T {
        self.0 as *const T
    }
}

impl<T> From<*mut T> for Address {
    fn from(ptr: *mut T) -> Self {
        Self(ptr as usize)
    }
}

impl<T> Into<*mut T> for Address {
    fn into(self) -> *mut T {
        self.0 as *mut T
    }
}
