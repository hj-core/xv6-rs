// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::dsa::ListNode;
use crate::lock::Spinlock;
use crate::mem::slab::Error::AllocateFromFullSlab;
use crate::HasHole;
use core::ptr;
use core::ptr::null_mut;
use core::sync::atomic::Ordering::Relaxed;
use wrapper::{Address, Bytes};

const CACHE_NAME_LENGTH: usize = 16;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_SLOTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

#[repr(C)]
struct Cache {
    /// [Cache] holes within the same [Cache] chain are circularly linked.
    hole: ListNode,
    /// Protect [Cache] from concurrent access.
    lock: Spinlock,
    name: [char; CACHE_NAME_LENGTH],
    slab_size: Bytes,
    /// slabs_* is the sentinel head of the circularly linked [Slab] holes.
    slabs_full: ListNode,
    slabs_partial: ListNode,
    slabs_empty: ListNode,
}

impl Cache {
    fn grow<T>(&mut self) -> Result<bool, Error>
    where
        T: Default + HasHole,
    {
        let addr0 = Self::request_contiguous_space(self.slab_size)?;
        let slab = unsafe {
            let ptr: *mut Slab = addr0.into();
            ptr.as_mut().unwrap()
        };
        slab.initialize::<T>(self.slab_size);

        let head = &mut self.slabs_empty;
        let next = unsafe { head.next.load(Relaxed).as_mut().unwrap() };
        let new = slab.hole();
        new.prev.store(head, Relaxed);
        new.next.store(next, Relaxed);
        head.next.store(new, Relaxed);
        next.prev.store(new, Relaxed);

        Ok(true)
    }

    fn request_contiguous_space(_size: Bytes) -> Result<Address, Error> {
        todo!()
    }
}

impl HasHole for Cache {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}

#[repr(C)]
#[derive(Debug)]
struct Slab {
    /// [Slab] holes within the same [Cache].slabs_* are circularly linked.
    hole: ListNode,
    /// Each bit represents slot usage (0: unused, 1: used).  
    /// The bits are packed: the first u64 represents slots 0-63,
    /// the second u64 represents slots 64-127, and so on.
    used_bitmap: [u64; SLAB_USED_BITMAP_SIZE],
    used_count: usize,
    slot0: Address,
    slot_size: Bytes,
    total_slots: usize,
}

impl Slab {
    fn initialize<T>(&mut self, slab_size: Bytes)
    where
        T: Default + HasHole,
    {
        self.unlink_hole();
        self.reset_used_bitmap_and_count();
        self.set_slot0_size_and_total::<T>(slab_size);
    }

    fn unlink_hole(&mut self) {
        self.hole().prev.store(null_mut(), Relaxed);
        self.hole().next.store(null_mut(), Relaxed);
    }

    fn reset_used_bitmap_and_count(&mut self) {
        for map in self.used_bitmap.iter_mut() {
            *map = 0;
        }
        self.used_count = 0;
    }

    fn set_slot0_size_and_total<T>(&mut self, slab_size: Bytes) {
        let slot0_offset = self.compute_slot0_offset::<T>();
        self.slot0 = Address::from(ptr::from_ref(self)) + slot0_offset;
        self.slot_size = Bytes(size_of::<T>());

        assert!(
            slot0_offset.0 + self.slot_size.0 <= slab_size.0,
            "Slab size is too small."
        );
        self.total_slots = (slab_size.0 - slot0_offset.0) % self.slot_size.0
    }

    /// Offset to slot0 from the address of [Slab].
    fn compute_slot0_offset<T>(&self) -> Bytes {
        let base: *const u8 = ptr::from_ref(self).cast();
        let header_size = size_of::<Slab>();
        let header_end = unsafe { base.byte_add(header_size) };
        let padding = header_end.align_offset(align_of::<T>());
        Bytes(header_size + padding)
    }

    /// Returns a reference to the object if allocation succeeds;
    /// otherwise, returns the corresponding error.
    fn allocate_object<T>(&mut self) -> Result<&mut T, Error>
    where
        T: Default + HasHole,
    {
        if self.is_full() {
            return Err(AllocateFromFullSlab);
        }
        let index = self.use_first_free_slot();
        let result = self.install_default::<T>(index);
        Ok(result)
    }

    fn is_full(&self) -> bool {
        self.used_count == self.total_slots
    }

    /// Mark the first free slot used and return its index.
    /// Panic if no free slots are available.
    fn use_first_free_slot(&mut self) -> usize {
        let mut result = 0;
        for map in self.used_bitmap.iter_mut() {
            if *map == 0xffff_ffff_ffff_ffff {
                result += 64;
                continue;
            }

            let shift = map.trailing_ones() as usize;
            result += shift;
            if result < self.total_slots {
                *map |= 1 << shift;
                self.used_count += 1;
            }
            break;
        }

        if result == self.total_slots {
            panic!("No free slots available.");
        }
        result
    }

    /// Install the default value of [T] to the target slot and return a mut reference to it.
    fn install_default<T>(&self, slot_index: usize) -> &mut T
    where
        T: Default + HasHole,
    {
        assert!(
            size_of::<T>() <= self.slot_size.0,
            "Can't fit object into slot."
        );
        let addr = self.slot0 + (self.slot_size * slot_index);
        let ptr: *mut T = addr.into();
        unsafe {
            ptr.write(T::default());
            ptr.as_mut().unwrap()
        }
    }
}

impl HasHole for Slab {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}

#[derive(Debug)]
enum Error {
    RequestMemoryFailed,
    AllocateFromFullSlab,
}

#[cfg(test)]
mod slab_tests {
    extern crate alloc;

    use super::*;
    use alloc::format;
    use core::sync::atomic::AtomicPtr;

    mod empty_slab {
        use super::*;

        fn new_empty() -> Slab {
            Slab {
                hole: ListNode {
                    prev: AtomicPtr::default(),
                    next: AtomicPtr::default(),
                },
                used_bitmap: [0; SLAB_USED_BITMAP_SIZE],
                used_count: 0,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: 128,
            }
        }

        #[test]
        fn test_new_empty() {
            let slab = new_empty();
            assert_slab_state_consistency(&slab);
        }

        #[test]
        fn test_use_first_free_slot() {
            let expected_return = 0;
            let mut expected_after = new_empty();
            expected_after.used_bitmap[0] = 1;
            expected_after.used_count = 1;

            let before = new_empty();
            assert_use_first_free_slot(expected_return, expected_after, before);
        }
    }

    mod full_slab {
        use super::*;

        fn new_full() -> Slab {
            Slab {
                hole: ListNode {
                    prev: AtomicPtr::default(),
                    next: AtomicPtr::default(),
                },
                used_bitmap: [
                    0xffff_ffff_ffff_ffff,
                    0xffff_ffff_ffff_ffff,
                    0xffff_ffff_ffff_ffff,
                    0xff,
                ],
                used_count: 200,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: 200,
            }
        }

        #[test]
        fn test_new_full() {
            let slab = new_full();
            assert_slab_state_consistency(&slab);
        }

        fn new_full_max_slots() -> Slab {
            Slab {
                hole: ListNode {
                    prev: AtomicPtr::default(),
                    next: AtomicPtr::default(),
                },
                used_bitmap: [0xffff_ffff_ffff_ffff; SLAB_USED_BITMAP_SIZE],
                used_count: MAX_SLOTS_PER_SLAB,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: MAX_SLOTS_PER_SLAB,
            }
        }

        #[test]
        fn test_new_full_max_slots() {
            let slab = new_full_max_slots();
            assert_slab_state_consistency(&slab);
        }

        #[test]
        #[should_panic(expected = "No free slots available.")]
        fn test_use_first_free_slot() {
            let return_irrelevant = 0xffff_ffff_ffff_ffff;
            let expected_after = new_full();
            let before = new_full();
            assert_use_first_free_slot(return_irrelevant, expected_after, before);
        }

        #[test]
        #[should_panic(expected = "No free slots available.")]
        fn test_use_first_free_slot_max_slots() {
            let return_irrelevant = 0xffff_ffff_ffff_ffff;
            let expected_after = new_full_max_slots();
            let before = new_full_max_slots();
            assert_use_first_free_slot(return_irrelevant, expected_after, before);
        }
    }

    mod partial_slab {
        use super::*;

        fn new_partial() -> Slab {
            Slab {
                hole: ListNode {
                    prev: AtomicPtr::default(),
                    next: AtomicPtr::default(),
                },
                used_bitmap: [
                    0xffff_ffff_ffff_ffff,
                    0x6030_0100_0000_08ff,
                    0x0f09_0f86_ea70_0010,
                    0x0,
                ],
                used_count: 100,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: 188,
            }
        }

        #[test]
        fn test_new_partial() {
            let slab = new_partial();
            assert_slab_state_consistency(&slab);
        }

        #[test]
        fn test_use_first_free_slot() {
            let expected_return = 72;
            let mut expected_after = new_partial();
            expected_after.used_bitmap[1] |= 1 << 8;
            expected_after.used_count += 1;

            let before = new_partial();
            assert_use_first_free_slot(expected_return, expected_after, before);
        }
    }

    fn assert_content_equal(slab1: &Slab, slab2: &Slab) {
        assert_eq!(
            slab1.hole.prev.load(Relaxed),
            slab2.hole.prev.load(Relaxed),
            "hole.prev"
        );
        assert_eq!(
            slab1.hole.next.load(Relaxed),
            slab2.hole.next.load(Relaxed),
            "hole.next"
        );
        assert_eq!(slab1.used_bitmap, slab2.used_bitmap, "used_bitmap");
        assert_eq!(slab1.used_count, slab2.used_count, "used_count");
        assert_eq!(slab1.slot0, slab2.slot0, "slot0");
        assert_eq!(slab1.slot_size, slab2.slot_size, "slot_size");
        assert_eq!(slab1.total_slots, slab2.total_slots, "total_slots");
    }

    fn assert_slab_state_consistency(slab: &Slab) {
        assert_used_bitmap_count_consistency(slab);
        assert_used_bitmap_total_slots_consistency(slab);
    }

    fn assert_used_bitmap_count_consistency(slab: &Slab) {
        let count = slab
            .used_bitmap
            .iter()
            .fold(0, |acc, &map| acc + (map.count_ones() as usize));
        assert_eq!(
            count, slab.used_count,
            "used_bitmap {:?} inconsistent with used_count {}",
            slab.used_bitmap, slab.used_count
        );
    }

    fn assert_used_bitmap_total_slots_consistency(slab: &Slab) {
        if slab.total_slots == MAX_SLOTS_PER_SLAB {
            return;
        }

        let map = slab.used_bitmap[slab.total_slots / 64];
        let i = slab.total_slots & 0x3f;
        for shift in i..64 {
            assert_eq!(
                0,
                map & (1 << shift),
                "used_bitmap {:?} inconsistent with total_slots {}",
                slab.used_bitmap,
                slab.total_slots
            );
        }
    }

    fn assert_use_first_free_slot(expected_return: usize, expected_after: Slab, mut before: Slab) {
        let str_before = format!("{before:?}");
        let actual_return = before.use_first_free_slot();
        assert_eq!(expected_return, actual_return, "{str_before}");

        let actual_after = before;
        assert_content_equal(&expected_after, &actual_after);
    }
}
