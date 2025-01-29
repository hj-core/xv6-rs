// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::lock::Spinlock;
use crate::mem::slab::Error::AllocateFromFullSlab;
use core::marker::PhantomData;
use core::marker::PhantomPinned;
use core::ptr;
use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;
use core::sync::atomic::Ordering::Relaxed;
use wrapper::{Address, Bytes};

const CACHE_NAME_LENGTH: usize = 16;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_SLOTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

#[repr(C)]
struct Cache<T>
where
    T: Default,
{
    /// Protect [Cache] from concurrent access.
    lock: Spinlock,
    name: [char; CACHE_NAME_LENGTH],
    pages_per_slab: usize,
    // slabs_* is null or circularly linked [SlabHead]s.
    slabs_full: AtomicPtr<SlabHeader<T>>,
    slabs_partial: AtomicPtr<SlabHeader<T>>,
    slabs_empty: AtomicPtr<SlabHeader<T>>,
}

impl<T> Cache<T>
where
    T: Default,
{
    /// Return a [SlabObject] if the allocation succeeds;
    /// otherwise, return the corresponding error.
    ///
    /// The allocated object has the default value of [T], and clients can access it through
    /// the [SlabObject].
    pub fn allocate_object() -> Result<SlabObject<T>, Error> {
        todo!()
    }

    fn grow(&mut self) -> Result<bool, Error> {
        todo!()
    }

    /// Ask the allocator for contiguous free pages.
    ///
    /// Return the starting address if the allocation succeeds;
    /// otherwise, return the corresponding error.
    fn request_contiguous_pages(_count: usize) -> Result<Address, Error> {
        todo!()
    }
}

#[repr(C)]
#[derive(Debug)]
struct SlabHeader<T>
where
    T: Default,
{
    /// Pointer to the source [Cache].
    ///
    /// This field also make [SlabHeader] ![Sync], ![Send] and is invariant over [T].
    source: *mut Cache<T>,
    /// [SlabHeader]s within the same [Cache].slabs_* are circularly linked.
    prev: AtomicPtr<SlabHeader<T>>,
    /// [SlabHeader]s within the same [Cache].slabs_* are circularly linked.
    next: AtomicPtr<SlabHeader<T>>,
    total_slots: usize,
    slot0: Address,
    slot_size: Bytes,
    /// Each bit represents slot usage (0: unused, 1: used).
    /// The bits are packed: the first u64 represents slots 0-63,
    /// the second u64 represents slots 64-127, and so on.
    used_bitmap: [u64; SLAB_USED_BITMAP_SIZE],
    used_count: usize,
    _marker: PhantomData<T>,
    _pinned: PhantomPinned,
}

impl<T> SlabHeader<T>
where
    T: Default,
{
    pub fn new_empty() -> Self {
        assert_ne!(0, size_of::<T>(), "Zero-size types are not supported.");

        Self {
            source: null_mut(),
            prev: AtomicPtr::new(null_mut()),
            next: AtomicPtr::new(null_mut()),
            total_slots: 0,
            slot0: Address(0),
            slot_size: Bytes(0),
            used_bitmap: [0; SLAB_USED_BITMAP_SIZE],
            used_count: 0,
            _marker: PhantomData,
            _pinned: PhantomPinned,
        }
    }

    fn initialize(&mut self, slab_size: Bytes) {
        assert_ne!(0, size_of::<T>(), "Zero-size types are not supported.");

        self.unlink();
        self.set_slot0_size_and_total(slab_size);
        self.reset_used_bitmap_and_count();
    }

    fn unlink(&mut self) {
        self.prev.store(null_mut(), Relaxed);
        self.next.store(null_mut(), Relaxed);
    }

    fn reset_used_bitmap_and_count(&mut self) {
        for map in self.used_bitmap.iter_mut() {
            *map = 0;
        }
        self.used_count = 0;
    }

    fn set_slot0_size_and_total(&mut self, slab_size: Bytes) {
        let slot0_offset = self.compute_slot0_offset();
        self.slot0 = Address::from(ptr::from_ref(self)) + slot0_offset;
        self.slot_size = Bytes(size_of::<T>());

        assert!(
            slot0_offset.0 + self.slot_size.0 <= slab_size.0,
            "Slab size is too small."
        );
        self.total_slots = (slab_size.0 - slot0_offset.0) / self.slot_size.0
    }

    /// Offset from the [SlabHeader]'s address to slot 0.
    /// This offset has considered the alignment requirement of object [T].
    fn compute_slot0_offset(&self) -> Bytes {
        let addr0 = Address(ptr::from_ref(self).addr());
        let header_size = Bytes(size_of::<SlabHeader<T>>());
        Self::compute_slot0_offset_helper(addr0, header_size)
    }

    fn compute_slot0_offset_helper(addr0: Address, header_size: Bytes) -> Bytes {
        let header_end = (addr0 + header_size).0;
        let object_align = align_of::<T>();
        let padding = if header_end % object_align == 0 {
            0
        } else {
            object_align - (header_end % object_align)
        };
        header_size + Bytes(padding)
    }

    /// Returns a [SlabObject] wrapping the allocated object [T] if the allocation succeeded;
    /// otherwise, returns the corresponding error.
    fn allocate_object(&mut self) -> Result<SlabObject<T>, Error> {
        if self.is_full() {
            return Err(AllocateFromFullSlab);
        }
        // This temporary value is not satisfactory because it takes up space other than the
        // reserved slot, but I have no idea how to construct the object directly over the
        // reserved slot.
        // One workaround is to make the object reusable: in the destructor of the SlabObject, we
        // restore the fields and relevant states of the underlying object so that it can be reused
        // by the next client.
        // This sounds unsafe, and I’m not sure if it outweighs the overhead of creating
        // a temporary value.
        let new_object = T::default();

        let slot_index = self.use_first_free_slot();
        // SAFETY:
        // * Each slot is properly aligned and large enough to contain an object of type T;
        //   each slot lies within the memory allocated for this Slab.
        // * These conditions are guaranteed during Slab initialization, therefore,
        //   writing the default value to the slot is safe.
        // * Both Slab and the object T are address-sensitive.
        // * Creating the SlabObject from the raw pointers of this Slab and the new object
        //   does not move the underlying Slab or object T.
        // * Returning the SlabObject does not move the underlying Slab or object T.
        unsafe {
            let object_ptr: *mut T = (self.slot0 + self.slot_size * slot_index).into();
            object_ptr.write(new_object);
            let result = SlabObject {
                source: AtomicPtr::new(ptr::from_mut(self)),
                object: AtomicPtr::from(object_ptr),
                _marker: PhantomData,
            };
            Ok(result)
        }
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

    fn deallocate_object(&mut self, _object: *mut T) {
        todo!()
    }
}

struct SlabObject<T>
where
    T: Default,
{
    source: AtomicPtr<SlabHeader<T>>,
    object: AtomicPtr<T>,
    _marker: PhantomData<T>,
}

/// A proxy to the actual allocated object.
/// This proxy provides a layer of protection to the underlying object, which is address-sensitive.
/// Dropping this object triggers the deallocation of the underlying object.
impl<T> SlabObject<T>
where
    T: Default,
{
    /// Get a shared reference to the underlying object.
    pub fn get_ref(&self) -> &T {
        // SAFETY:
        // * The object field is not publicly exposed.
        // * Since SlabObject is only created through Slab allocations, which should
        //   correctly initialize this field, we can safely dereference it.
        // * Dereferencing the raw pointer to get a shared reference does not move
        //   the underlying object.
        unsafe { &*self.object.load(Relaxed) }
    }

    /// Get an exclusive reference to the underlying object.
    ///
    /// # SAFETY:
    ///
    /// The underlying object [T] is address-sensitive; therefore, clients of this function
    /// must ensure the object hasn't been moved.
    /// See [Module pin](https://doc.rust-lang.org/beta/core/pin/index.html) for more details.
    pub unsafe fn get_mut(&mut self) -> &mut T {
        // SAFETY:
        // * The object field is not publicly exposed.
        // * Since SlabObject is only created through Slab allocations, which should
        //   correctly initialize this field, we can safely dereference it.
        // * Dereferencing the raw pointer to get an exclusive reference does not
        //   move the underlying object.
        &mut *self.object.load(Relaxed)
    }
}

impl<T> Drop for SlabObject<T>
where
    T: Default,
{
    fn drop(&mut self) {
        // SAFETY:
        // * The source field is not publicly exposed.
        // * Since SlabObject is only created through Slab allocations, which should
        //   correctly initialize source field, we can safely dereference it.
        // * The deallocate_object method should do the cleanup properly.
        unsafe {
            (*self.source.load(Relaxed)).deallocate_object(self.object.load(Relaxed));
        }
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

    mod object_ignorance {
        use super::*;
        use core::any::type_name;

        #[test]
        fn test_compute_slot0_offset_helper() {
            let expected = Bytes(5);
            let addr0 = Address(0x0);
            let header_size = Bytes(5);
            assert_compute_slot0_offset_helper::<u8>(expected, addr0, header_size);

            let expected = Bytes(23);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(16);
            assert_compute_slot0_offset_helper::<u64>(expected, addr0, header_size);

            let expected = Bytes(31);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(22);
            assert_compute_slot0_offset_helper::<u128>(expected, addr0, header_size);

            let expected = Bytes(31);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(28);
            assert_compute_slot0_offset_helper::<u128>(expected, addr0, header_size);

            let expected = Bytes(30);
            let addr0 = Address(0x8000_fff2);
            let header_size = Bytes(28);
            assert_compute_slot0_offset_helper::<u128>(expected, addr0, header_size);
        }

        fn assert_compute_slot0_offset_helper<T: Default>(
            expected: Bytes,
            addr0: Address,
            header_size: Bytes,
        ) {
            let actual = SlabHeader::<T>::compute_slot0_offset_helper(addr0, header_size);
            assert_eq!(
                expected,
                actual,
                "addr0= {addr0:?}, header_size= {header_size:?}, type= {:?}",
                type_name::<T>()
            );
        }
    }

    mod empty_slab {
        use super::*;

        fn new_empty() -> SlabHeader<u64> {
            SlabHeader {
                source: null_mut(),
                prev: AtomicPtr::new(null_mut()),
                next: AtomicPtr::new(null_mut()),
                used_bitmap: [0; SLAB_USED_BITMAP_SIZE],
                used_count: 0,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: 128,
                _marker: PhantomData,
                _pinned: PhantomPinned,
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

        fn new_full() -> SlabHeader<u64> {
            SlabHeader {
                source: null_mut(),
                prev: AtomicPtr::new(null_mut()),
                next: AtomicPtr::new(null_mut()),
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
                _marker: PhantomData,
                _pinned: PhantomPinned,
            }
        }

        #[test]
        fn test_new_full() {
            let slab = new_full();
            assert_slab_state_consistency(&slab);
        }

        fn new_full_max_slots() -> SlabHeader<u64> {
            SlabHeader {
                source: null_mut(),
                prev: AtomicPtr::new(null_mut()),
                next: AtomicPtr::new(null_mut()),
                used_bitmap: [0xffff_ffff_ffff_ffff; SLAB_USED_BITMAP_SIZE],
                used_count: MAX_SLOTS_PER_SLAB,
                slot0: Address(0),
                slot_size: Bytes(0),
                total_slots: MAX_SLOTS_PER_SLAB,
                _marker: PhantomData,
                _pinned: PhantomPinned,
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

        fn new_partial() -> SlabHeader<u64> {
            SlabHeader {
                source: null_mut(),
                prev: AtomicPtr::new(null_mut()),
                next: AtomicPtr::new(null_mut()),
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
                _marker: PhantomData,
                _pinned: PhantomPinned,
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

    fn assert_content_equal(slab1: &SlabHeader<u64>, slab2: &SlabHeader<u64>) {
        assert_eq!(
            slab1.prev.load(Relaxed),
            slab2.prev.load(Relaxed),
            "pinpoint.link1"
        );
        assert_eq!(
            slab1.next.load(Relaxed),
            slab2.next.load(Relaxed),
            "pinpoint.link2"
        );
        assert_eq!(slab1.used_bitmap, slab2.used_bitmap, "used_bitmap");
        assert_eq!(slab1.used_count, slab2.used_count, "used_count");
        assert_eq!(slab1.slot0, slab2.slot0, "slot0");
        assert_eq!(slab1.slot_size, slab2.slot_size, "slot_size");
        assert_eq!(slab1.total_slots, slab2.total_slots, "total_slots");
    }

    fn assert_slab_state_consistency(slab: &SlabHeader<u64>) {
        assert_used_bitmap_count_consistency(slab);
        assert_used_bitmap_total_slots_consistency(slab);
    }

    fn assert_used_bitmap_count_consistency(slab: &SlabHeader<u64>) {
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

    fn assert_used_bitmap_total_slots_consistency(slab: &SlabHeader<u64>) {
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

    fn assert_use_first_free_slot(
        expected_return: usize,
        expected_after: SlabHeader<u64>,
        mut before: SlabHeader<u64>,
    ) {
        let str_before = format!("{before:?}");
        let actual_return = before.use_first_free_slot();
        assert_eq!(expected_return, actual_return, "{str_before}");

        let actual_after = before;
        assert_content_equal(&expected_after, &actual_after);
    }
}
