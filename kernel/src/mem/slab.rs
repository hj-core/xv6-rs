// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::mem::slab::Error::{
    AllocateFromFullSlab, SlabNotAligned, SlabTooSmall, ZeroSizeTypeNotSupported,
};
use core::alloc::Layout;
use core::marker::PhantomData;
use core::marker::PhantomPinned;
use core::ptr::null_mut;
use core::sync::atomic::AtomicPtr;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};
use wrapper::{Address, Bytes};

const CACHE_NAME_LENGTH: usize = 16;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_SLOTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

#[repr(C)]
struct Cache<T>
where
    T: Default,
{
    name: [char; CACHE_NAME_LENGTH],
    slab_layout: Layout,
    // `slabs_*` is either null or the head of the doubly linked [SlabHeader]s.
    slabs_full: AtomicPtr<SlabHeader<T>>,
    slabs_partial: AtomicPtr<SlabHeader<T>>,
    slabs_empty: AtomicPtr<SlabHeader<T>>,
}

impl<T> Cache<T>
where
    T: Default,
{
    /// Returns a [SlabObject] wrapping the allocated object [T] if the allocation succeeds,
    /// or else returns the corresponding error.
    ///
    /// The allocated object has the default value of [T], and clients can access it through
    /// the [SlabObject].
    ///
    /// # SAFETY:
    /// * todo!()
    unsafe fn allocate_object(_cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        todo!()
    }

    /// Returns true if the attempt to deallocate the [SlabObject] succeeds,
    /// or else returns the corresponding error.
    ///
    /// # SAFETY:
    /// * todo!()
    unsafe fn deallocate_object(
        _cache: *mut Cache<T>,
        _object: &SlabObject<T>,
    ) -> Result<bool, Error> {
        todo!()
    }

    /// Attempts to create a new slab and push it to the `slab_empty`.
    /// Clients of this method are responsible for acquiring the required memory
    /// and providing the starting address `addr0`.
    ///
    /// Returns a pointer to the newly created [SlabHeader] if the attempt succeeds,
    /// or returns the corresponding error if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned, the provided memory
    /// remain unmodified.
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    /// * `addr0` must point to a memory block that satisfies the `slab_layout` and dedicated
    ///   to the new slab.
    ///
    /// # THREAD SAFETY:
    /// * This method is **NOT** thread-safe.
    unsafe fn grow(cache: *mut Cache<T>, addr0: Address) -> Result<*mut SlabHeader<T>, Error> {
        // SAFETY:
        // * Dereferencing `cache` is safe because it is a valid pointer.
        // * [Layout] implements [Copy] so there is no ownership transfer.
        let layout = unsafe { (*cache).slab_layout };
        if addr0.0 % layout.align() != 0 {
            return Err(SlabNotAligned);
        }

        // SAFETY:
        // * We are safe to call the `new` function because we have satisfied its safety contract.
        // * We are safe to dereference `cache` and update it in place since it is a valid pointer.
        // * We are safe to dereference the newly returned [SlabHeader] pointer and update it in
        //   place.
        // * We are safe to dereference `slab_empty` and update it in place if it is not null.
        // * In light of the above, this unsafe block is considered safe.
        unsafe {
            let result = SlabHeader::new(cache, Bytes(layout.size()), addr0)?;

            let old_head = (*cache).slabs_empty.load(Acquire);
            if !old_head.is_null() {
                (*result).next.store(old_head, Release);
                (*old_head).prev.store(result, Release);
            }
            (*cache).slabs_empty.store(result, Release);

            Ok(result)
        }
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
    /// This field also makes [SlabHeader] ![Sync] ![Send] and invariant over [T].
    source: *mut Cache<T>,
    /// [SlabHeader]s within the same [Cache].slabs_* are doubly linked.
    prev: AtomicPtr<SlabHeader<T>>,
    /// [SlabHeader]s within the same [Cache].slabs_* are doubly linked.
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
    /// Attempts to create a slab for `cache` at `addr0` with a size of `slab_size`.
    ///
    /// Returns a pointer to the [SlabHeader] if the attempt succeeds,
    /// or an [Error] if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned, the provided memory
    /// remain unmodified.
    ///
    /// # SAFETY:
    /// * The memory block starting at `addr0` and extending for `slab_size` must be dedicated
    ///   to the new slab's use.
    unsafe fn new(
        cache: *mut Cache<T>,
        slab_size: Bytes,
        addr0: Address,
    ) -> Result<*mut Self, Error> {
        if size_of::<T>() == 0 {
            return Err(ZeroSizeTypeNotSupported);
        }

        if addr0.0 % align_of::<SlabHeader<T>>() != 0 {
            return Err(SlabNotAligned);
        }

        let header_size = Bytes(size_of::<SlabHeader<T>>());
        let slot_size = Bytes(size_of::<T>());
        let slot0_offset = Self::compute_slot0_offset(addr0, header_size);
        let min_size = slot0_offset + slot_size;

        if slab_size.0 < min_size.0 {
            return Err(SlabTooSmall);
        }

        let total_slots = (slab_size.0 - slot0_offset.0) / slot_size.0;
        let slot0 = addr0 + slot0_offset;

        let header = SlabHeader {
            source: cache,
            prev: AtomicPtr::new(null_mut()),
            next: AtomicPtr::new(null_mut()),
            total_slots,
            slot0,
            slot_size,
            used_bitmap: [0; SLAB_USED_BITMAP_SIZE],
            used_count: 0,
            _marker: PhantomData,
            _pinned: PhantomPinned,
        };

        let result: *mut SlabHeader<T> = addr0.into();
        // SAFETY:
        // * We are safe to write the newly created header to `result` because
        //   1. We have checked the alignment requirement.
        //   2. We have verified the intended slab size can accommodate the header
        //      plus at least one slot.
        //   3. The memory block is dedicated to this slab's use.
        unsafe { result.write(header) };

        Ok(result)
    }

    /// Offset from the [SlabHeader]'s address to slot 0.
    /// This offset has considered the alignment requirement of object [T].
    fn compute_slot0_offset(addr0: Address, header_size: Bytes) -> Bytes {
        let header_end = (addr0 + header_size).0;
        let object_align = align_of::<T>();
        let padding = if header_end % object_align == 0 {
            0
        } else {
            object_align - (header_end % object_align)
        };
        header_size + Bytes(padding)
    }

    /// Attempts to allocate an object from the underlying slab.
    ///
    /// Returns a [SlabObject] wrapping the allocated object [T] if the allocation succeeds,
    /// or returns the corresponding error if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned, the states of `header`
    /// remain unmodified.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn allocate_object(header: *mut SlabHeader<T>) -> Result<SlabObject<T>, Error> {
        if SlabHeader::is_full(header) {
            return Err(AllocateFromFullSlab);
        }
        // This temporary value is not satisfactory because it takes up space other than the
        // reserved slot, but I have no idea how to construct the object directly over the
        // reserved slot.
        // One workaround is to make the object reusable: in the destructor of the SlabObject, we
        // restore the fields and relevant states of the underlying object so that it can be reused
        // by the next client.
        // This sounds unsafe, and I’m not sure if it outweighs the overhead of creating
        // a temporary value and moving to the slot.
        let new_object = T::default();

        let slot_index = SlabHeader::use_first_free_slot(header)?;
        // SAFETY:
        // * We are safe to dereference `header` because it is a valid pointer.
        // * We are safe to write the `new_object` to the `object_ptr` because
        //   1. Each slot lies within the memory allocated for this slab.
        //   2. Each slot is properly aligned and large enough to contain an object of type T.
        //   3. The computed `slot_index` for this object should be correct.
        let object_ptr = unsafe {
            let ptr: *mut T = ((*header).slot0 + (*header).slot_size * slot_index).into();
            ptr.write(new_object);
            ptr
        };

        let result = SlabObject {
            source: AtomicPtr::new(header),
            object: AtomicPtr::new(object_ptr),
            _marker: PhantomData,
        };
        Ok(result)
    }

    /// Returns whether the slab this [SlabHeader] refers to is full.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn is_full(header: *mut SlabHeader<T>) -> bool {
        (*header).used_count == (*header).total_slots
    }

    /// Attempts to mark the first free slot as used.
    ///
    /// Returns the index of the free slot if the attempt succeeds,
    /// or returns the corresponding [Error] if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned, the states of `header`
    /// remain unmodified.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn use_first_free_slot(header: *mut SlabHeader<T>) -> Result<usize, Error> {
        // SAFETY:
        // * We are safe to deference `header` and mutate its fields in place because
        //   it is a valid pointer.
        let mut result = 0;
        for map in (*header).used_bitmap.iter_mut() {
            if *map == 0xffff_ffff_ffff_ffff {
                result += 64;
                continue;
            }

            let shift = map.trailing_ones() as usize;
            result += shift;

            if result < (*header).total_slots {
                *map |= 1 << shift;
                (*header).used_count += 1;
                return Ok(result);
            }
        }

        assert!(
            SlabHeader::is_full(header),
            "`used_bitmap` is inconsistent with fn `is_full`"
        );
        Err(AllocateFromFullSlab)
    }

    /// Attempts to deallocate the `object` from the slab the `header` refers to.
    ///
    /// Returns true if the attempt succeeds, or returns the corresponding error if it fails.
    ///
    /// # SAFETY:
    /// * todo!()
    unsafe fn deallocate_object(
        _header: *mut SlabHeader<T>,
        _object: *mut T,
    ) -> Result<bool, Error> {
        todo!()
    }
}

#[derive(Debug)]
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
        // * SlabObject is only created through Cache allocation,
        //   which should correctly initialize the source field.
        // * The source field is private to the SlabObject,
        //   and we haven't exposed any methods to mutate it,
        //   so it's supposed to retain its initial value.
        // * A SlabHeader should have its source field correctly set.
        // * The Cache and SlabHeader should live longer than this SlabObject.
        // * Therefore, we are safe to dereference the source field to get the SlabHeader,
        //   and further dereference its source field to get the Cache.
        // * There are no moves of values.
        // * There are no concerns regarding exception safety.
        unsafe {
            let cache = (*self.source.load(Relaxed)).source;
            let _ = Cache::deallocate_object(cache, &self);
        }
    }
}

#[derive(Debug, PartialEq)]
enum Error {
    SlabNotAligned,
    SlabTooSmall,
    ZeroSizeTypeNotSupported,
    RequestMemoryFailed,
    AllocateFromFullSlab,
}

#[cfg(test)]
mod cache_tests {
    extern crate alloc;
    use super::*;
    use crate::mem::PAGE_SIZE;
    use alloc::alloc::{alloc, dealloc};
    use alloc::format;
    use alloc::vec::Vec;

    fn new_test_default<T: Default>() -> Cache<T> {
        Cache::<T> {
            name: ['c'; CACHE_NAME_LENGTH],
            slab_layout: Layout::from_size_align(PAGE_SIZE.0, align_of::<SlabHeader<T>>()).unwrap(),
            slabs_full: Default::default(),
            slabs_partial: Default::default(),
            slabs_empty: Default::default(),
        }
    }

    /// Calls `alloc` with the `layout` `count` times and
    /// returns a collection of the returned pointers.
    fn acquire_memory(layout: Layout, count: usize) -> Vec<*mut u8> {
        assert!(0 < layout.size(), "Zero size not supported");
        let mut result = Vec::with_capacity(count);
        for _ in 0..count {
            // SAFETY:
            // * We are safe to call `alloc` with `layout`
            //   because we have checked that the `layout` has a non-zero size.
            let addr0 = unsafe { alloc(layout) };
            assert!(!addr0.is_null(), "Failed to allocate memory");
            result.push(addr0);
        }
        result
    }

    /// Calls `dealloc` with each pointer in `ptrs` using the `layout`.
    ///
    /// # SAFETY:
    /// * Each `(ptr, layout)` pair must satisfy the safety contract of `dealloc`.
    unsafe fn release_memory(ptrs: Vec<*mut u8>, layout: Layout) {
        for ptr in ptrs {
            unsafe { dealloc(ptr, layout) };
        }
    }

    /// Asserts that `used_bitmap` and `used_count` describe an empty slab.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    fn assert_slab_empty<T: Default>(header: *const SlabHeader<T>) {
        assert!(!header.is_null());
        // SAFETY:
        // * We are safe to dereference `header` and mutate it in place
        //   because it is a valid pointer.
        unsafe {
            assert_eq!(0, (*header).used_count);
            (*header).used_bitmap.iter().for_each(|&i| assert_eq!(0, i));
        }
    }

    #[test]
    fn grow_succeeds_update_slabs_empty() {
        type T = u64;
        let mut cache = new_test_default::<T>();

        let addrs = acquire_memory(cache.slab_layout, 10);
        {
            let result = unsafe { Cache::grow(&raw mut cache, addrs[0].into()) };
            assert!(result.is_ok_and(|ptr| ptr.addr() == addrs[0].addr()));
            assert!(cache.slabs_full.load(Relaxed).is_null());
            assert!(cache.slabs_partial.load(Relaxed).is_null());

            let head_empty = cache.slabs_empty.load(Relaxed);
            assert_slab_empty(head_empty);
            assert_eq!(&raw mut cache, unsafe { (*head_empty).source });
            assert_eq!(addrs[0].addr(), head_empty.addr());

            let prev = unsafe { (*head_empty).prev.load(Relaxed) };
            assert!(prev.is_null());

            let next = unsafe { (*head_empty).next.load(Relaxed) };
            assert!(next.is_null());
        }

        {
            let result = unsafe { Cache::grow(&raw mut cache, addrs[1].into()) };
            assert!(result.is_ok_and(|ptr| ptr.addr() == addrs[1].addr()));
            assert!(cache.slabs_full.load(Relaxed).is_null());
            assert!(cache.slabs_partial.load(Relaxed).is_null());

            let head_empty = cache.slabs_empty.load(Relaxed);
            assert_slab_empty(head_empty);
            assert_eq!(&raw mut cache, unsafe { (*head_empty).source });
            assert_eq!(addrs[1].addr(), head_empty.addr());

            let prev = unsafe { (*head_empty).prev.load(Relaxed) };
            assert!(prev.is_null());

            let next = unsafe { (*head_empty).next.load(Relaxed) };
            assert!(!next.is_null());
            assert_eq!(addrs[0].addr(), next.addr());

            let next_prev = unsafe { (*next).prev.load(Relaxed) };
            assert_eq!(head_empty, next_prev);
            let next_next = unsafe { (*next).next.load(Relaxed) };
            assert!(next_next.is_null());
        }

        {
            for i in 2..addrs.len() {
                let result = unsafe { Cache::grow(&raw mut cache, addrs[i].into()) };
                assert!(result.is_ok_and(|ptr| ptr.addr() == addrs[i].addr()));
                assert!(cache.slabs_full.load(Relaxed).is_null());
                assert!(cache.slabs_partial.load(Relaxed).is_null());

                let head_empty = cache.slabs_empty.load(Relaxed);
                assert_slab_empty(head_empty);
                assert_eq!(&raw mut cache, unsafe { (*head_empty).source });
                assert_eq!(addrs[i].addr(), head_empty.addr());
            }

            let mut count = addrs.len();
            let mut prev = null_mut();
            let mut curr = cache.slabs_empty.load(Relaxed);
            while !curr.is_null() {
                count -= 1;
                assert_eq!(addrs[count].addr(), curr.addr());
                prev = curr;
                curr = unsafe { (*curr).next.load(Relaxed) };
            }
            assert_eq!(0, count);
            assert_eq!(addrs[0].addr(), prev.addr());

            while !prev.is_null() {
                assert_eq!(addrs[count].addr(), prev.addr());
                curr = prev;
                prev = unsafe { (*prev).prev.load(Relaxed) };
                count += 1;
            }
            assert_eq!(addrs.len(), count);
            assert_eq!(addrs[addrs.len() - 1].addr(), curr.addr());
        }
        unsafe { release_memory(addrs, cache.slab_layout) }
    }

    #[test]
    fn grow_with_insufficient_size_return_size_err() {
        type T = u64;
        let mut cache = new_test_default::<T>();
        {
            let small_layout =
                Layout::from_size_align(size_of::<SlabHeader<T>>(), align_of::<SlabHeader<u64>>())
                    .unwrap();
            cache.slab_layout = small_layout;
        }
        let addrs = acquire_memory(cache.slab_layout, 1);

        let result = unsafe { Cache::grow(&raw mut cache, addrs[0].into()) };
        let result_str = format!("{:?}", result);
        assert!(
            result.is_err_and(|err| matches!(err, SlabTooSmall)),
            "Expected Err({SlabTooSmall:?}) but got {result_str}."
        );
        assert!(cache.slabs_full.load(Relaxed).is_null());
        assert!(cache.slabs_partial.load(Relaxed).is_null());
        assert!(cache.slabs_empty.load(Relaxed).is_null());

        unsafe { release_memory(addrs, cache.slab_layout) }
    }

    #[test]
    fn grow_with_wrong_align_return_align_err() {
        type T = u64;
        let mut cache = new_test_default::<T>();

        let addrs = acquire_memory(cache.slab_layout, 1);

        let result = unsafe { Cache::grow(&raw mut cache, Address(addrs[0].addr() + 1)) };
        let result_str = format!("{:?}", result);
        assert!(
            result.is_err_and(|err| matches!(err, SlabNotAligned)),
            "Expected Err({SlabNotAligned:?}) but got {result_str}."
        );
        assert!(cache.slabs_full.load(Relaxed).is_null());
        assert!(cache.slabs_partial.load(Relaxed).is_null());
        assert!(cache.slabs_empty.load(Relaxed).is_null());

        unsafe { release_memory(addrs, cache.slab_layout) }
    }
}

#[cfg(test)]
mod header_tests {
    extern crate alloc;

    use super::*;

    mod object_ignorance {
        use super::*;
        use core::any::type_name;

        #[test]
        fn test_compute_slot0_offset() {
            let expected = Bytes(5);
            let addr0 = Address(0x0);
            let header_size = Bytes(5);
            assert_compute_slot0_offset::<u8>(expected, addr0, header_size);

            let expected = Bytes(23);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(16);
            assert_compute_slot0_offset::<u64>(expected, addr0, header_size);

            let expected = Bytes(31);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(22);
            assert_compute_slot0_offset::<u128>(expected, addr0, header_size);

            let expected = Bytes(31);
            let addr0 = Address(0x8000_fff1);
            let header_size = Bytes(28);
            assert_compute_slot0_offset::<u128>(expected, addr0, header_size);

            let expected = Bytes(30);
            let addr0 = Address(0x8000_fff2);
            let header_size = Bytes(28);
            assert_compute_slot0_offset::<u128>(expected, addr0, header_size);
        }

        fn assert_compute_slot0_offset<T: Default>(
            expected: Bytes,
            addr0: Address,
            header_size: Bytes,
        ) {
            let actual = SlabHeader::<T>::compute_slot0_offset(addr0, header_size);
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
        type T = u32;

        fn new_test_empty() -> SlabHeader<T> {
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
        fn new_test_empty_has_consistent_state() {
            let mut header = new_test_empty();
            unsafe { assert_slab_state_consistency(&raw mut header) };
        }

        #[test]
        fn test_use_first_free_slot() {
            let expected_return = Ok(0);
            let mut expected_after = new_test_empty();
            expected_after.used_bitmap[0] = 1;
            expected_after.used_count = 1;

            let mut before = new_test_empty();
            unsafe {
                assert_use_first_free_slot(
                    expected_return,
                    &raw mut expected_after,
                    &raw mut before,
                )
            }
        }
    }

    mod full_slab {
        use super::*;
        type T = u64;

        fn new_test_full() -> SlabHeader<T> {
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
        fn new_test_full_has_consistent_state() {
            let mut slab = new_test_full();
            unsafe { assert_slab_state_consistency(&raw mut slab) };
        }

        fn new_test_full_max_slots() -> SlabHeader<T> {
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
        fn new_test_full_max_slots_has_consistent_state() {
            let mut slab = new_test_full_max_slots();
            unsafe { assert_slab_state_consistency(&raw mut slab) }
        }

        #[test]
        fn test_use_first_free_slot() {
            let expected_return = Err(AllocateFromFullSlab);
            let mut expected_after = new_test_full();
            let mut before = new_test_full();
            unsafe {
                assert_use_first_free_slot(
                    expected_return,
                    &raw mut expected_after,
                    &raw mut before,
                )
            }
        }

        #[test]
        fn test_use_first_free_slot_max_slots() {
            let expected_return = Err(AllocateFromFullSlab);
            let mut expected_after = new_test_full_max_slots();
            let mut before = new_test_full_max_slots();
            unsafe {
                assert_use_first_free_slot(
                    expected_return,
                    &raw mut expected_after,
                    &raw mut before,
                )
            }
        }
    }

    mod partial_slab {
        use super::*;
        type T = u128;

        fn new_test_partial() -> SlabHeader<T> {
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
        fn new_test_partial_has_consistent_state() {
            let mut header = new_test_partial();
            unsafe { assert_slab_state_consistency(&raw mut header) };
        }

        #[test]
        fn test_use_first_free_slot() {
            let expected_return = Ok(72);
            let mut expected_after = new_test_partial();
            expected_after.used_bitmap[1] |= 1 << 8;
            expected_after.used_count += 1;

            let mut before = new_test_partial();
            unsafe {
                assert_use_first_free_slot(
                    expected_return,
                    &raw mut expected_after,
                    &raw mut before,
                )
            }
        }
    }

    /// # SAFETY:
    /// * `header1` and `header2` must be valid pointers.
    unsafe fn assert_content_equal<T: Default>(
        header1: *const SlabHeader<T>,
        header2: *const SlabHeader<T>,
    ) {
        assert_eq!(
            (*header1).prev.load(Relaxed),
            (*header2).prev.load(Relaxed),
            "prev"
        );
        assert_eq!(
            (*header1).next.load(Relaxed),
            (*header2).next.load(Relaxed),
            "next"
        );
        assert_eq!(
            (*header1).used_bitmap,
            (*header2).used_bitmap,
            "used_bitmap"
        );
        assert_eq!((*header1).used_count, (*header2).used_count, "used_count");
        assert_eq!((*header1).slot0, (*header2).slot0, "slot0");
        assert_eq!((*header1).slot_size, (*header2).slot_size, "slot_size");
        assert_eq!(
            (*header1).total_slots,
            (*header2).total_slots,
            "total_slots"
        );
    }

    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn assert_slab_state_consistency<T: Default>(header: *mut SlabHeader<T>) {
        assert_ne!(0, size_of::<T>(), "Zero size type not supported");
        assert!(0 < (*header).total_slots, "Zero total_slots");
        assert_used_bitmap_count_consistency(header);
        assert_used_bitmap_total_slots_consistency(header);
    }

    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn assert_used_bitmap_count_consistency<T: Default>(header: *const SlabHeader<T>) {
        let count = (*header)
            .used_bitmap
            .iter()
            .fold(0, |acc, &map| acc + (map.count_ones() as usize));
        assert_eq!(
            count,
            (*header).used_count,
            "used_bitmap {:?} inconsistent with used_count {}",
            (*header).used_bitmap,
            (*header).used_count
        );
    }

    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn assert_used_bitmap_total_slots_consistency<T: Default>(header: *const SlabHeader<T>) {
        if (*header).total_slots == MAX_SLOTS_PER_SLAB {
            return;
        }

        // Check that all the bits corresponding to slots after `total_slots` are zeros.
        let map = (*header).used_bitmap[(*header).total_slots / 64];
        let i = (*header).total_slots & 0x3f;
        for shift in i..64 {
            assert_eq!(
                0,
                map & (1 << shift),
                "used_bitmap {:?} inconsistent with total_slots {}",
                (*header).used_bitmap,
                (*header).total_slots
            );
        }
    }

    /// # SAFETY:
    /// * `expected_after` and `before` must be valid pointers.
    unsafe fn assert_use_first_free_slot<T: Default>(
        expected_return: Result<usize, Error>,
        expected_after: *mut SlabHeader<T>,
        before: *mut SlabHeader<T>,
    ) {
        let actual_return = SlabHeader::use_first_free_slot(before);
        assert_eq!(
            expected_return, actual_return,
            "Expected {expected_return:?} but got {actual_return:?}",
        );

        let actual_after = before;
        assert_content_equal(expected_after, actual_after);
    }
}
