// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

#![allow(unsafe_op_in_unsafe_fn)]

use core::alloc::Layout;
use core::marker::PhantomData;
use core::marker::PhantomPinned;
use core::ptr;
use core::ptr::{null_mut, NonNull};
use Error::{AllocateFromFullSlab, AllocateFromNullSlab, NotAnObjectOfCurrentSlab};

type ByteSize = usize;

const CACHE_NAME_LENGTH: usize = 16;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_SLOTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

/// todo!()
///
/// Methods of [Cache] are not thread-safe; therefore client need to provide
/// proper synchronization measures.
///
/// # Safety:
/// * [T] must not be repr(packed).
#[repr(C)]
struct Cache<T>
where
    T: Default,
{
    name: [char; CACHE_NAME_LENGTH],
    slab_layout: Layout,
    // `slabs_*` is either null or the head of the doubly linked [SlabHeader]s.
    slabs_full: *mut SlabHeader<T>,
    slabs_partial: *mut SlabHeader<T>,
    slabs_empty: *mut SlabHeader<T>,
}

impl<T> Cache<T>
where
    T: Default,
{
    /// `new` returns a new [Cache] with the given `name` and `slab_layout`.
    /// The `slab_layout` must have a size no less than [Cache::min_slab_size]
    /// and comply with the [Cache::align_of_slab].
    fn new(name: [char; CACHE_NAME_LENGTH], slab_layout: Layout) -> Self {
        if size_of::<T>() == 0 {
            panic!("Cache::new: zero size type is not supported")
        };
        if slab_layout.align() % Self::align_of_slab() != 0 {
            panic!("Cache::new: slab_layout is not properly aligned")
        };
        if slab_layout.size() < Self::min_slab_size() {
            panic!("Cache::new: slab_layout should not smaller than Cache::min_slab_size")
        }

        Self {
            name,
            slab_layout,
            slabs_full: null_mut(),
            slabs_partial: null_mut(),
            slabs_empty: null_mut(),
        }
    }

    /// `min_slab_size` returns the minimum size of the slab layout for type [T].
    /// Note that the value is evaluated a bit conservatively.
    fn min_slab_size() -> usize {
        size_of::<SlabHeader<T>>() + align_of::<T>() + size_of::<T>()
    }

    /// `align_of_slab` returns the alignment that the slab layout must comply with.
    fn align_of_slab() -> usize {
        align_of::<SlabHeader<T>>()
    }

    /// `allocate_object` returns a [SlabObject] wrapping the allocated object
    /// if the allocation succeeds; otherwise, it returns the corresponding error.
    ///
    /// It is guaranteed that if an [Error] is returned, the `cache` remains unmodified.
    /// The allocated object has the default value of [T], and clients can access it
    /// through the [SlabObject].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn allocate_object(cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        assert!(!cache.is_null(), "`cache` should not be null");

        if !(*cache).slabs_partial.is_null() {
            Self::allocate_from_partial(cache)
        } else if !(*cache).slabs_empty.is_null() {
            Self::allocate_from_empty(cache)
        } else if !(*cache).slabs_full.is_null() {
            Err(AllocateFromFullSlab)
        } else {
            Err(AllocateFromNullSlab)
        }
    }

    /// `allocate_from_empty` attempts to allocate an object from one of the empty slabs.
    ///
    /// It returns a [SlabObject] wrapping the allocated object if the attempt succeeds,
    /// or returns the corresponding [Error] if it fails.
    ///
    /// It is guaranteed that if an [Error] is returned, the states of `cache`
    /// remain unmodified.
    /// The allocated object has the default value of [T], and clients can access it
    /// through the [SlabObject].
    ///
    /// # Safety:
    /// * `cache` must be a valid pointer.
    unsafe fn allocate_from_empty(cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        assert!(!cache.is_null(), "`cache` should not be null");

        if (*cache).slabs_empty.is_null() {
            return Err(AllocateFromNullSlab);
        }

        let result = SlabHeader::allocate_object((*cache).slabs_empty)?;

        // Update list heads
        let (detached_node, new_head_empty) = Cache::pop_front((*cache).slabs_empty);
        (*cache).slabs_empty = new_head_empty;

        if SlabHeader::is_full(detached_node) {
            (*cache).slabs_full = Cache::push_front((*cache).slabs_full, detached_node);
        } else {
            (*cache).slabs_partial = Cache::push_front((*cache).slabs_partial, detached_node);
        }

        // EXCEPTION SAFETY:
        // * `is_full` and `pop_front` is not going to panic:
        //   - As long as `slabs_empty` is updated correctly, it will be either null
        //     or a valid pointer without its `prev` linked.
        //   - We have checked that `slabs_empty` is not null.
        // * `push_front` is not going to panic:
        //   - `detached_node` is isolated as long as `pop_front` is implemented correctly.
        //   - As long as `slabs_full` and `slabs_partial` are updated correctly, they will be
        //     either null or valid pointers without their `prev` linked.
        // * Therefore, if the allocation from `old_head_empty` is `Ok`, we can reach this code
        //   and resume `cache` to a valid state.
        Ok(result)
    }

    /// `push_front` pushes the `node` to the front of `head` and returns the new head.
    ///
    /// # SAFETY:
    /// * `head` should be either null or a valid pointer that doesn't have its `prev` linked.
    /// * `node` should be either null or a valid pointer that is isolated, i.e., not linked to other nodes.
    unsafe fn push_front(head: *mut SlabHeader<T>, node: *mut SlabHeader<T>) -> *mut SlabHeader<T> {
        if !head.is_null() {
            assert_eq!(
                null_mut(),
                (*head).prev,
                "`head` should not have its `prev` linked"
            )
        }

        if !node.is_null() {
            assert_eq!(
                null_mut(),
                (*node).prev,
                "`node` is not isolated: it has its `prev` linked"
            );
            assert_eq!(
                null_mut(),
                (*node).next,
                "`node` is not isolated: it has its `next` linked"
            );
        }

        if head.is_null() {
            return node;
        };
        if node.is_null() {
            return head;
        };

        (*node).next = head;
        (*head).prev = node;
        node
    }

    /// Detaches the first node from `head` and returns the detached node and the new head.
    ///
    /// # SAFETY:
    /// * `head` should be a valid pointer if it is not null.
    /// * `head` should not have its `prev` linked if it is not null.
    unsafe fn pop_front(head: *mut SlabHeader<T>) -> (*mut SlabHeader<T>, *mut SlabHeader<T>) {
        if head.is_null() {
            return (null_mut(), null_mut());
        }

        assert_eq!(
            null_mut(),
            (*head).prev,
            "`head` should not have its `prev` linked"
        );

        let new_head = (*head).next;
        if !new_head.is_null() {
            (*new_head).prev = null_mut();
        }
        (*head).next = null_mut();

        (head, new_head)
    }

    /// Attempts to allocate an object from one of the partial slabs.
    ///
    /// Returns a [SlabObject] wrapping the allocated object [T] if the attempt succeeds,
    /// or returns the corresponding [Error] if it fails.
    /// Furthermore, it is guaranteed that if an [Error] is returned, the states of `cache`
    /// remain unmodified.
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    /// * Clients need to apply thread-safe measures to protect the `cache` from concurrent access.
    unsafe fn allocate_from_partial(cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        assert!(!cache.is_null(), "`cache` should not be null");

        if (*cache).slabs_partial.is_null() {
            return Err(AllocateFromNullSlab);
        }

        let result = SlabHeader::allocate_object((*cache).slabs_partial)?;

        // Update list heads if the slab became full
        if SlabHeader::is_full((*cache).slabs_partial) {
            let (detached_node, new_head_partial) = Cache::pop_front((*cache).slabs_partial);
            (*cache).slabs_partial = new_head_partial;
            (*cache).slabs_full = Cache::push_front((*cache).slabs_full, detached_node);
        }

        // EXCEPTION SAFETY:
        // * `is_full` and `pop_front` are not going to panic:
        //   - As long as `slabs_partial` is updated correctly, it will be either null
        //     or a valid pointer without its `prev` linked.
        //   - We have checked that `slabs_partial` is not null.
        // * `push_front` is not going to panic:
        //   - `detached_node` is isolated as long as `pop_front` is implemented correctly.
        //   - As long as `slabs_full` is updated correctly, it will be either null
        //     or a valid pointer without its `prev` linked.
        // * Therefore, if the allocation from `slabs_partial` is [Ok], we can reach this code
        //   and resume `cache` to a valid state.
        Ok(result)
    }

    /// `deallocate_object` attempts to deallocate the given allocated object.
    /// It returns true if the attempt succeeds; otherwise, it returns the corresponding [Error].
    ///
    /// # Safety:
    /// * `cache` must be a valid pointer.
    /// * `slab_object` must be allocated from `cache`.
    unsafe fn deallocate_object(
        cache: *mut Cache<T>,
        slab_object: SlabObject<T>,
    ) -> Result<bool, Error> {
        if cache.is_null() {
            panic!("Cache::deallocate_object: cache should not be null");
        }
        if (*slab_object.source).source != cache {
            panic!("Cache::deallocate_object: object does not belong to the cache");
        }

        // Update the header
        let header = slab_object.source;
        let result = unsafe { SlabHeader::deallocate_object(header, slab_object)? };
        assert!(
            result,
            "Cache::deallocate_object: SlabHeader::deallocate_object should return true"
        );

        // Update the slab lists
        if header == (*cache).slabs_full {
            (*cache).slabs_full = (*header).next;
        } else if header == (*cache).slabs_partial {
            (*cache).slabs_partial = (*header).next;
        } else if header == (*cache).slabs_empty {
            panic!("Cache::deallocate_object: The slab header should never be slab_empty")
        }
        Cache::detach_node_from_list(header);

        if (*header).used_count == 0 {
            (*cache).slabs_empty = Cache::push_front((*cache).slabs_empty, header);
        } else if (*header).used_count < (*header).total_slots {
            (*cache).slabs_partial = Cache::push_front((*cache).slabs_partial, header);
        } else {
            panic!(
                "Cache::deallocate_object: The slab after deallocation should have a used_count less than the total_slots"
            )
        }

        Ok(true)
    }

    /// Detaches the `node` from the slab list it belonged to.
    ///
    /// # Safety:
    /// * `node` must be a valid pointer.
    unsafe fn detach_node_from_list(node: *mut SlabHeader<T>) {
        if node.is_null() {
            panic!("Cache::detach_node_from_list: `node` should not be null")
        }
        if !(*node).prev.is_null() {
            (*(*node).prev).next = (*node).next;
        }
        if !(*node).next.is_null() {
            (*(*node).next).prev = (*node).prev;
        }
        (*node).prev = null_mut();
        (*node).next = null_mut();
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
    unsafe fn grow(cache: *mut Cache<T>, addr0: NonNull<u8>) -> Result<*mut SlabHeader<T>, Error> {
        if addr0.align_offset((*cache).slab_layout.align()) != 0 {
            panic!("Cache::grow: addr0 should comply with the slab layout")
        }

        // SAFETY:
        // * We are safe to call the `new` function because we have satisfied its safety contract.
        // * We are safe to dereference `cache` and update it in place since it is a valid pointer.
        // * We are safe to dereference the newly returned [SlabHeader] pointer and update it in
        //   place.
        // * We are safe to dereference `slab_empty` and update it in place if it is not null.
        // * In light of the above, this unsafe block is considered safe.
        let result = SlabHeader::new(cache, (*cache).slab_layout.size(), addr0);

        let old_head = (*cache).slabs_empty;
        if !old_head.is_null() {
            (*result).next = old_head;
            (*old_head).prev = result;
        }
        (*cache).slabs_empty = result;

        Ok(result)
    }

    /// `shrink` attempts to reclaim memory from the `cache`.
    /// It returns a pointer to the evicted empty slab if there is one;
    /// otherwise, it returns a null pointer.
    unsafe fn shrink(cache: *mut Cache<T>) -> *mut u8 {
        if (*cache).slabs_empty.is_null() {
            return null_mut();
        }

        let result = (*cache).slabs_empty;
        (*cache).slabs_empty = (*result).next;
        Cache::detach_node_from_list(result);
        result as *mut u8
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
    prev: *mut SlabHeader<T>,
    /// [SlabHeader]s within the same [Cache].slabs_* are doubly linked.
    next: *mut SlabHeader<T>,
    total_slots: usize,
    slot0: NonNull<u8>,
    slot_size: ByteSize,
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
    /// Returns a pointer to the [SlabHeader] if the attempt succeeds, or an [Error] if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned, the provided memory remains unmodified.
    ///
    /// # SAFETY:
    /// * The memory block starting at `addr0` and extending for `slab_size` must be dedicated
    ///   to the new slab's use.
    unsafe fn new(cache: *mut Cache<T>, slab_size: ByteSize, addr0: NonNull<u8>) -> *mut Self {
        let header_size: ByteSize = size_of::<SlabHeader<T>>();
        let slot_size: ByteSize = size_of::<T>();
        let slot0_offset = Self::compute_slot0_offset(addr0.addr().get(), header_size);
        let total_slots = (slab_size - slot0_offset) / slot_size;

        // SAFETY:
        // * todo!()
        let slot0 = unsafe { addr0.add(slot0_offset) };

        let header = Self {
            source: cache,
            prev: null_mut(),
            next: null_mut(),
            total_slots,
            slot0,
            slot_size,
            used_bitmap: [0; SLAB_USED_BITMAP_SIZE],
            used_count: 0,
            _marker: PhantomData,
            _pinned: PhantomPinned,
        };

        let result: *mut SlabHeader<T> = addr0.as_ptr().cast();
        unsafe { result.write(header) };

        result
    }

    /// Offset from the [SlabHeader]'s address to slot 0.
    /// This offset has considered the alignment requirement of object [T].
    fn compute_slot0_offset(addr0: usize, header_size: ByteSize) -> ByteSize {
        let header_end = addr0 + header_size;
        let object_align = align_of::<T>();
        let padding: ByteSize = if header_end % object_align == 0 {
            0
        } else {
            object_align - (header_end % object_align)
        };
        header_size + padding
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
            let ptr: *mut T = (*header)
                .slot0
                .add((*header).slot_size * slot_index)
                .as_ptr()
                .cast();
            ptr.write(new_object);
            ptr
        };

        let result = SlabObject {
            source: header,
            object: object_ptr,
            _marker: PhantomData,
        };
        Ok(result)
    }

    /// `is_full` returns whether the underlying slab is full.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn is_full(header: *mut SlabHeader<T>) -> bool {
        (*header).used_count == (*header).total_slots
    }

    /// `use_first_free_slot` attempts to mark the first free slot as used.
    ///
    /// The index of the free slot is returned if the attempt succeeds,
    /// or an [Err] is returned if it fails.
    /// Furthermore, it is guaranteed that if an [Err] is returned,
    /// the `header` remains unmodified.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn use_first_free_slot(header: *mut SlabHeader<T>) -> Result<usize, Error> {
        let first_free_slot = SlabHeader::<T>::first_free_slot(&(*header).used_bitmap);
        if (*header).total_slots <= first_free_slot {
            return Err(AllocateFromNullSlab);
        }

        (*header).used_count += 1;
        SlabHeader::<T>::alter_used_bit(&mut (*header).used_bitmap, first_free_slot);
        Ok(first_free_slot)
    }

    fn first_free_slot(used_bitmap: &[u64; SLAB_USED_BITMAP_SIZE]) -> usize {
        let mut result = 0;
        for &segment in used_bitmap.iter() {
            if segment != 0xffff_ffff_ffff_ffff {
                result += segment.trailing_ones() as usize;
                break;
            }
            result += 64;
        }
        result
    }

    fn alter_used_bit(used_bitmap: &mut [u64; SLAB_USED_BITMAP_SIZE], slot_index: usize) {
        if MAX_SLOTS_PER_SLAB <= slot_index {
            panic!("`slot_index` should be less than the `MAX_SLOTS_PER_SLAB`");
        }
        let (index, shift) = (slot_index / 64, slot_index % 64);
        used_bitmap[index] ^= 1 << shift;
    }

    /// `deallocate_object` attempts to deallocate the allocated object.
    /// It returns true if the attempt succeeds; otherwise, it returns the corresponding [Error].
    ///
    /// It is guaranteed that if an [Err] is returned, the header remains unmodified.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    /// * `slab_object` must be allocated from `header`.
    unsafe fn deallocate_object(
        header: *mut SlabHeader<T>,
        slab_object: SlabObject<T>,
    ) -> Result<bool, Error> {
        if header.is_null() {
            panic!("SlabHeader::deallocate_object: header should not be null");
        }
        if header != slab_object.source {
            return Err(NotAnObjectOfCurrentSlab);
        };

        let slot_index = unsafe {
            Self::object_slot_index(
                (*header).slot0.addr().get(),
                (*header).slot_size,
                (*header).total_slots,
                slab_object.object.addr(),
            )?
        };

        if unsafe {
            !Self::is_slot_in_use(&(*header).used_bitmap, (*header).total_slots, slot_index)
        } {
            panic!("SlabHeader::deallocate_object: deallocate from an unused slot");
        };

        Self::alter_used_bit(&mut (*header).used_bitmap, slot_index);
        (*header).used_count -= 1;

        Ok(true)
    }

    /// `object_slot_index` returns the slot index of the object or the corresponding error.
    fn object_slot_index(
        slot0_addr: usize,
        slot_size: ByteSize,
        total_slots: usize,
        object_addr: usize,
    ) -> Result<usize, Error> {
        if object_addr < slot0_addr {
            return Err(NotAnObjectOfCurrentSlab);
        }

        let offset = object_addr - slot0_addr;
        if offset % slot_size != 0 {
            return Err(NotAnObjectOfCurrentSlab);
        };

        let index = offset / slot_size;
        if total_slots <= index {
            return Err(NotAnObjectOfCurrentSlab);
        }

        Ok(index)
    }

    /// `is_slot_in_use` returns whether the slot with `slot_index` is in use.
    fn is_slot_in_use(
        used_bitmap: &[u64; SLAB_USED_BITMAP_SIZE],
        total_slots: usize,
        slot_index: usize,
    ) -> bool {
        if total_slots <= slot_index {
            panic!("The `slot_index` is out of bounds");
        };

        let (index, shift) = (slot_index / 64, slot_index % 64);
        used_bitmap[index] & (1 << shift) > 0
    }
}

/// A proxy to the actual allocated object, which is address-sensitive.
///
/// When done with the object, the client needs to call the `deallocate_object` method of [Cache]
/// with this [SlabObject].
/// Failing to do so will cause a memory leak; the destructor of the object will still be invoked
/// when this [SlabObject] is dropped.
#[derive(Debug)]
pub struct SlabObject<T>
where
    T: Default,
{
    source: *mut SlabHeader<T>,
    object: *mut T,
    _marker: PhantomData<T>,
}

unsafe impl<T> Send for SlabObject<T> where T: Default + Send {}
unsafe impl<T> Sync for SlabObject<T> where T: Default + Send {}

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
        unsafe { &*self.object }
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
        &mut *self.object
    }
}

impl<T> Drop for SlabObject<T>
where
    T: Default,
{
    fn drop(&mut self) {
        // SAFETY:
        // * The `object` field remain unmodified since allocation because we have not exposed
        //   it or methods to mutate it.
        // * The `object` field should have initialized with a valid pointer, so it is nonnull,
        //   aligned, and safe for both reads and writes.
        // * The only safe way for client to access the underlying object [T] is through this
        //   [SlabObject].
        //   When this [SlabObject] is dropped, client should have done with the object [T] and
        //   satisfied any invariants related to the object, so we are safe to drop the object [T].
        unsafe { ptr::drop_in_place(self.object) }
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    AllocateFromFullSlab,
    AllocateFromNullSlab,
    NotAnObjectOfCurrentSlab,
}

#[cfg(test)]
mod cache_tests {
    extern crate alloc;
    extern crate std;
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use test_utils::*;

    fn new_test_default<T: Default>() -> Cache<T> {
        Cache::<T> {
            name: ['c'; CACHE_NAME_LENGTH],
            slab_layout: Layout::from_size_align(
                safe_slab_size::<T>(2),
                align_of::<SlabHeader<T>>(),
            )
            .expect("Failed to create the `slab_layout`"),
            slabs_full: null_mut(),
            slabs_partial: null_mut(),
            slabs_empty: null_mut(),
        }
    }

    #[test]
    fn push_front_with_null_head_and_node_return_null() {
        type T = u8;
        let result = unsafe { Cache::<T>::push_front(null_mut(), null_mut()) };
        assert_eq!(null_mut(), result, "The new head should be null")
    }

    #[test]
    #[should_panic(expected = "`head` should not have its `prev` linked")]
    fn push_front_with_prev_linked_head_should_panic() {
        // Create a `head` with its `prev` linked
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let prev = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).prev = prev;
            (*prev).next = head;
        }

        // Exercise `push_front`
        unsafe { Cache::push_front(head, null_mut()) };
    }

    #[test]
    fn push_front_with_valid_head_and_null_node_return_head() {
        // Create a `head` containing two nodes
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let next = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = next;
            (*next).prev = head;
        }

        // Exercise `push_front`
        let new_head = unsafe { Cache::<T>::push_front(head, null_mut()) };

        // Verify the new head
        assert_eq!(new_head, head, "The new head should be the original `head`");
        assert_eq!(
            2,
            unsafe { size_of_list(new_head) },
            "The new head should contain two nodes"
        );
        assert!(
            unsafe { contains_node(new_head, head) },
            "The new head should contain the `head`"
        );
        assert!(
            unsafe { contains_node(new_head, next) },
            "The new head should contain the `next`"
        );
        unsafe { verify_list_doubly_linked(new_head) };
    }

    #[test]
    fn push_front_with_valid_head_and_node_return_node() {
        // Create a `head` containing two nodes
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let next = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = next;
            (*next).prev = head;
        }

        // Create the `node` to be inserted
        let node = slab_man.new_test_slab(null_mut());

        // Exercise `push_front`
        let new_head = unsafe { Cache::push_front(head, node) };

        // Verify the new head
        assert_eq!(node, new_head, "The new head should be the `node`");
        assert_eq!(
            3,
            unsafe { size_of_list(new_head) },
            "The new head should contain three nodes"
        );
        assert!(
            unsafe { contains_node(new_head, node) },
            "The new head should contains `node`"
        );
        assert!(
            unsafe { contains_node(new_head, head) },
            "The new head should contain `head`"
        );
        assert!(
            unsafe { contains_node(new_head, next) },
            "The new head should contain `next`"
        );
        unsafe { verify_list_doubly_linked(new_head) };
    }

    #[test]
    #[should_panic(expected = "`node` is not isolated: it has its `prev` linked")]
    fn push_front_with_prev_linked_node_should_panic() {
        // Create a `node` with its `prev` linked
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let node = slab_man.new_test_slab(null_mut());
        let prev = slab_man.new_test_slab(null_mut());
        unsafe {
            (*node).prev = prev;
            (*prev).next = node;
        }

        // Exercise `push_front`
        unsafe { Cache::push_front(null_mut(), node) };
    }

    #[test]
    #[should_panic(expected = "`node` is not isolated: it has its `next` linked")]
    fn push_front_with_next_linked_node_should_panic() {
        // Create a `node` with its `next` linked
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let node = slab_man.new_test_slab(null_mut());
        let next = slab_man.new_test_slab(null_mut());
        unsafe {
            (*node).next = next;
            (*next).prev = node;
        }

        // Exercise `push_front`
        unsafe { Cache::push_front(null_mut(), node) };
    }

    #[test]
    fn pop_front_with_null_head_return_nulls() {
        type T = u8;
        let (node, new_head) = unsafe { Cache::<T>::pop_front(null_mut()) };
        assert_eq!(
            null_mut(),
            node,
            "The detached node should be null but got {node:?}"
        );
        assert_eq!(
            null_mut(),
            new_head,
            "The new head should be null but got {new_head:?}"
        );
    }

    #[test]
    #[should_panic(expected = "`head` should not have its `prev` linked")]
    fn pop_front_with_prev_linked_head_should_panic() {
        // Create a `head` with its `prev` linked
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let prev = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).prev = prev;
            (*prev).next = head;
        }

        // Exercise `pop_front`
        unsafe { Cache::pop_front(head) };
    }

    #[test]
    fn pop_front_with_single_node_head_return_head_and_null() {
        // Create a `head` containing a single node
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());

        // Exercise `pop_front`
        let (node, new_head) = unsafe { Cache::<T>::pop_front(head) };

        // Verify the detached node
        assert_eq!(
            node, head,
            "The detached node should be the original `head`"
        );
        unsafe { verify_node_isolated(node) };

        // Verify the new head
        assert_eq!(null_mut(), new_head, "The new head should be null");
    }

    #[test]
    fn pop_front_with_multi_nodes_head_return_head_and_next() {
        // Create a `head` containing three nodes
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let next = slab_man.new_test_slab(null_mut());
        let next_next = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = next;
            (*next).prev = head;
            (*next).next = next_next;
            (*next_next).prev = next;
        }

        // Exercise `pop_front`
        let (node, new_head) = unsafe { Cache::pop_front(head) };

        // Verify the detached node
        assert_eq!(node, head, "The detached node should be the original head");
        unsafe { verify_node_isolated(node) };

        // Verify the new head
        assert_eq!(
            next, new_head,
            "The new head should be the `next` of the original `head`"
        );
        assert_eq!(
            2,
            unsafe { size_of_list(new_head) },
            "The new head should contain two nodes"
        );
        assert!(
            unsafe { contains_node(new_head, next_next) },
            "The new head should contain the `next_next`"
        );
        unsafe { verify_list_doubly_linked(new_head) };
    }

    #[test]
    #[should_panic(expected = "Cache::detach_node_from_list: `node` should not be null")]
    fn detach_node_from_list_with_null_node_should_panic() {
        type T = TestObject;
        unsafe { Cache::<T>::detach_node_from_list(null_mut()) }
    }

    #[test]
    fn detach_node_from_list_with_isolated_node() {
        // Create an empty slab
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let node = slab_man.new_test_slab(null_mut());

        // Exercise `detach_node_from_list`
        unsafe { Cache::detach_node_from_list(node) };

        // Verify the result
        unsafe { verify_node_isolated(node) };
    }

    #[test]
    fn detach_node_from_list_with_head_node() {
        // Create a list containing three nodes
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let body = slab_man.new_test_slab(null_mut());
        let tail = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = body;
            (*body).prev = head;
            (*body).next = tail;
            (*tail).prev = body;
        }

        // Exercise `detach_node_from_list`
        unsafe { Cache::detach_node_from_list(head) };

        // Verify the resulting node and list
        unsafe {
            verify_node_isolated(head);
            verify_list_doubly_linked(body);
            assert_eq!(
                tail,
                (*body).next,
                "The `next` of the `body` should be the `tail`"
            );
            assert_eq!(
                2,
                size_of_list(body),
                "The resulting list should contain two nodes"
            )
        }
    }

    #[test]
    fn detach_node_from_list_with_tail_node() {
        // Create a list containing three nodes
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let body = slab_man.new_test_slab(null_mut());
        let tail = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = body;
            (*body).prev = head;
            (*body).next = tail;
            (*tail).prev = body;
        }

        // Exercise `detach_node_from_list`
        unsafe { Cache::detach_node_from_list(tail) };

        // Verify the resulting node and list
        unsafe {
            verify_node_isolated(tail);
            verify_list_doubly_linked(head);
            assert_eq!(
                body,
                (*head).next,
                "The `next` of the `head` should be the `body`"
            );
            assert_eq!(
                2,
                size_of_list(head),
                "The resulting list should contain two nodes"
            )
        }
    }

    #[test]
    fn detach_node_from_list_with_body_node() {
        // Create a list containing three nodes
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let head = slab_man.new_test_slab(null_mut());
        let body = slab_man.new_test_slab(null_mut());
        let tail = slab_man.new_test_slab(null_mut());
        unsafe {
            (*head).next = body;
            (*body).prev = head;
            (*body).next = tail;
            (*tail).prev = body;
        }

        // Exercise `detach_node_from_list`
        unsafe { Cache::detach_node_from_list(body) };

        // Verify the resulting node and list
        unsafe {
            verify_node_isolated(body);
            verify_list_doubly_linked(head);
            assert_eq!(
                tail,
                (*head).next,
                "The `next` of the `head` should be the `tail`"
            );
            assert_eq!(
                2,
                size_of_list(head),
                "The resulting list should contain two nodes"
            )
        }
    }

    #[test]
    #[should_panic(expected = "`cache` should not be null")]
    fn allocate_object_with_null_cache_should_panic() {
        type T = TestObject;
        let _ = unsafe { Cache::<T>::allocate_object(null_mut()) };
    }

    #[test]
    #[should_panic(expected = "`cache` should not be null")]
    fn allocate_from_empty_with_null_cache_should_panic() {
        type T = u64;
        let _ = unsafe { Cache::<T>::allocate_from_empty(null_mut()) };
    }

    #[test]
    fn allocate_from_empty_when_no_empty_slabs_return_null_err() {
        // Create a `cache` containing a partial slab
        type T = u128;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        let _slab_object1 = unsafe { SlabHeader::allocate_object(only_slab) }
            .expect("Failed to allocate object from the `only_slab`");
        cache.slabs_partial = only_slab;

        // Exercise `allocate_from_empty` and verify the result
        let result = unsafe { Cache::allocate_from_empty(&raw mut cache) };
        assert!(
            result.is_err(),
            "The result should be Err(AllocateFromNullSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, AllocateFromNullSlab),
            "The error should be {:?} but got {err:?});",
            AllocateFromNullSlab,
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let slabs_after = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        assert_eq!(
            vec![_slab_object1.object.addr()],
            allocated_objects_after,
            "The `cache` should have the same objects allocated before and after"
        );
    }

    #[test]
    fn allocate_from_empty_with_single_empty_multi_slots_slab() {
        // Create a `cache` containing a single empty slab that has multiple slots
        type T = TestObject;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = only_slab;
        assert!(
            unsafe { (*only_slab).total_slots > 1 },
            "Slab for this test should have a `total_slots` greater than one"
        );

        // Exercise `allocate_from_empty` and verify the result
        let result = unsafe { Cache::allocate_from_empty(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert_eq!(
            only_slab, slab_object.source,
            "`source` of the allocated [SlabObject] should be the `only_slab`",
        );
        assert_eq!(
            &TestObject::default(),
            slab_object.get_ref(),
            "The object behind the allocated [SlabObject] should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let slabs_after = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        assert_eq!(
            vec![slab_object.object.addr()],
            allocated_objects_after,
            "The `cache` should only have the object behind the `slab_object` allocated"
        );
    }

    #[test]
    fn allocate_from_empty_with_single_empty_single_slot_slab() {
        // Create a `cache` containing a single empty slab that has only one slot
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");

        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = only_slab;
        assert_eq!(
            1,
            unsafe { (*only_slab).total_slots },
            "Slab for this test should have a `total_slots` of one"
        );

        // Exercise `allocate_from_empty` and verify the result
        let result = unsafe { Cache::allocate_from_empty(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert_eq!(
            only_slab, slab_object.source,
            "`source` of the allocated [SlabObject] should be the `only_slab`",
        );
        assert_eq!(
            &TestObject::default(),
            slab_object.get_ref(),
            "The object behind the allocated [SlabObject] should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let slabs_after = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        assert_eq!(
            vec![slab_object.object.addr()],
            allocated_objects_after,
            "The `cache` should only have the object behind the [SlabObject] allocated"
        );
    }

    #[test]
    fn allocate_from_empty_with_empty_and_partial_multi_slots_slabs() {
        // Create a `cache` containing one partial slab and two empty slabs
        type T = TestObject;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let slab0 = slab_man.new_test_slab(&raw mut cache);
        let slab1 = slab_man.new_test_slab(&raw mut cache);
        unsafe {
            (*slab0).next = slab1;
            (*slab1).prev = slab0;
        }
        cache.slabs_empty = slab0;

        let slab2 = slab_man.new_test_slab(&raw mut cache);
        let _slab_object1 = unsafe { SlabHeader::allocate_object(slab2) }
            .expect("Failed to allocate object from `slab2`");
        cache.slabs_partial = slab2;

        assert!(
            unsafe { (*slab2).total_slots > 1 },
            "Slab for this test should have a `total_slots` greater than one"
        );

        // Exercise `allocate_from_empty` and verify the result
        let result = unsafe { Cache::allocate_from_empty(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert!(
            slab_object.source == slab0 || slab_object.source == slab1,
            "`source` of the allocated [SlabObject] should be either `slab0` or `slab1`"
        );
        assert_eq!(
            &TestObject::default(),
            slab_object.get_ref(),
            "The object behind the allocated [SlabObject] should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let mut slabs_before = vec![slab0, slab1, slab2];
        slabs_before.sort();
        let mut slabs_after = unsafe { cache_slabs(&raw mut cache) };
        slabs_after.sort();
        assert_eq!(
            slabs_after, slabs_before,
            "The `cache` should have the same slabs before and after"
        );

        let mut expected_allocated_objects =
            vec![slab_object.object.addr(), _slab_object1.object.addr()];
        expected_allocated_objects.sort();
        let mut actual_allocated_objects = unsafe { cache_allocated_addrs(&raw mut cache) };
        actual_allocated_objects.sort();
        assert_eq!(
            expected_allocated_objects, actual_allocated_objects,
            "The `cache` should have the expected objects allocated"
        );
    }

    #[test]
    #[should_panic(expected = "`cache` should not be null")]
    fn allocate_from_partial_with_null_cache_should_panic() {
        type T = u128;
        let _ = unsafe { Cache::<T>::allocate_from_partial(null_mut()) };
    }

    #[test]
    fn allocate_from_partial_when_no_partial_slabs_return_null_err() {
        // Create a `cache` that contains a full slab and an empty slab.
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");

        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let empty_slab = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = empty_slab;

        let full_slab = slab_man.new_test_slab(&raw mut cache);
        let _slab_object1 = unsafe { SlabHeader::allocate_object(full_slab) }
            .expect("Failed to allocate object from `full_slab`");
        cache.slabs_full = full_slab;

        assert_eq!(
            1,
            unsafe { (*full_slab).total_slots },
            "Slab for this test should have a `total_slots` of one"
        );

        // Exercise `allocate_from_partial` and verify the returned result
        let result = unsafe { Cache::allocate_from_partial(&raw mut cache) };
        assert!(
            result.is_err(),
            "The result should be Err(AllocateFromNullSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, AllocateFromNullSlab),
            "The error should be {:?} but got {err:?}",
            AllocateFromNullSlab,
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let mut slab_before = vec![empty_slab, full_slab];
        slab_before.sort();
        let mut slab_after = unsafe { cache_slabs(&raw mut cache) };
        slab_after.sort();
        assert_eq!(
            slab_before, slab_after,
            "The `cache` should have the same slabs before and after"
        );

        let allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        assert_eq!(
            vec![_slab_object1.object.addr()],
            allocated_objects_after,
            "The `cache` should only have the object behind the `slab_object` allocated"
        );
    }

    #[test]
    fn allocate_from_partial_when_single_partial_slab_with_multi_free_slots() {
        // Create a `cache` containing a single partial slab, which has multiple free slots remaining
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(4), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");

        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        let _slab_object1 = unsafe { SlabHeader::allocate_object(only_slab) }
            .expect("Failed to allocate `_slab_object1` from `only_slab`");
        let _slab_object2 = unsafe { SlabHeader::allocate_object(only_slab) }
            .expect("Failed to allocate `_slab_object2` from `only_slab`");

        let free_slots = unsafe { (*only_slab).total_slots - (*only_slab).used_count };
        assert!(
            free_slots > 1,
            "`only_slab` should have multiple free slots remaining; otherwise, this test is incorrect"
        );
        cache.slabs_partial = only_slab;

        // Exercise `allocate_from_partial` and verify the result
        let result = unsafe { Cache::allocate_from_partial(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert_eq!(
            only_slab, slab_object.source,
            "`source` of the allocated [SlabObject] should be the `only_slab`"
        );
        assert_eq!(
            &T::default(),
            slab_object.get_ref(),
            "The object behind the allocated [SlabObject] should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let slabs_after = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let mut expected_allocated_objects = vec![
            slab_object.object.addr(),
            _slab_object1.object.addr(),
            _slab_object2.object.addr(),
        ];
        expected_allocated_objects.sort();
        let mut allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        allocated_objects_after.sort();
        assert_eq!(
            expected_allocated_objects, allocated_objects_after,
            "The `cache` should have the expected objects allocated"
        );
    }

    #[test]
    fn allocate_from_partial_when_single_partial_slab_with_single_free_slot() {
        // Create a `cache` containing a single partial slab, which has a single free slot remaining
        type T = TestObject;
        let slab_size = safe_slab_size::<T>(2);
        let slab_layout = Layout::from_size_align(slab_size, align_of::<SlabHeader<T>>())
            .expect("Failed to create `slab_layout`");

        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        let slab_object1 = unsafe { SlabHeader::allocate_object(only_slab) }
            .expect("Failed to allocate object from the `only_slab`");
        cache.slabs_partial = only_slab;

        assert_eq!(
            2,
            unsafe { (*only_slab).total_slots },
            "Test slab should have a `total_slots` of two; otherwise, this test is incorrect"
        );

        // Exercise `allocate_from_partial` and verify the result
        let result = unsafe { Cache::allocate_from_partial(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert_eq!(
            only_slab, slab_object.source,
            "`source` of the allocated [SlabObject] should be the `only_slab`"
        );
        assert_eq!(
            &T::default(),
            slab_object.get_ref(),
            "The object behind the [SlabObject] should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let slabs_after = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let mut expected_allocated_objects =
            vec![slab_object.object.addr(), slab_object1.object.addr()];
        expected_allocated_objects.sort();
        let mut allocated_objects_after = unsafe { cache_allocated_addrs(&raw mut cache) };
        allocated_objects_after.sort();
        assert_eq!(
            expected_allocated_objects, allocated_objects_after,
            "The `cache` should have the expected objects allocated"
        );
    }

    #[test]
    fn allocate_from_partial_when_multi_partial_slabs_with_single_free_slot() {
        // Create a `cache` containing a full slab, an empty slab and two partial slabs.
        // Each partial slab has only one free slot remaining.
        type T = TestObject;
        let slab_size = safe_slab_size::<T>(2);
        let slab_layout = Layout::from_size_align(slab_size, align_of::<SlabHeader<T>>())
            .expect("Failed to create `slab_layout`");

        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;
        let mut slab_man = SlabMan::new(cache.slab_layout);

        let empty_slab = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = empty_slab;

        assert_eq!(
            2,
            unsafe { (*empty_slab).total_slots },
            "Test slab should have a `total_slots` of two; otherwise, this test is incorrect"
        );

        let partial_slab1 = slab_man.new_test_slab(&raw mut cache);
        let _slab_object1 = unsafe { SlabHeader::allocate_object(partial_slab1) }
            .expect("Failed to allocate object from `partial_slab1`");
        let partial_slab2 = slab_man.new_test_slab(&raw mut cache);
        let _slab_object2 = unsafe { SlabHeader::allocate_object(partial_slab2) }
            .expect("Failed to allocate object from `partial_slab2`");
        unsafe {
            (*partial_slab1).next = partial_slab2;
            (*partial_slab2).prev = partial_slab1;
        }
        cache.slabs_partial = partial_slab1;

        let full_slab = slab_man.new_test_slab(&raw mut cache);
        let _slab_object3 = unsafe { SlabHeader::allocate_object(full_slab) }
            .expect("Failed to allocate object from `full_slab`");
        let _slab_object4 = unsafe { SlabHeader::allocate_object(full_slab) }
            .expect("Failed to allocate another object from `full_slab`");
        cache.slabs_full = full_slab;

        // Exercise `allocate_from_partial` and verify the result
        let result = unsafe { Cache::allocate_from_partial(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");

        // Verify the allocated [SlabObject]
        let slab_object = result.unwrap();
        assert!(
            slab_object.source == partial_slab1 || slab_object.source == partial_slab2,
            "`source` of the allocated [SlabObject] should be either `partial_slab1` or `partial_slab2`"
        );
        assert_eq!(
            &T::default(),
            slab_object.get_ref(),
            "The allocated object should have the default value"
        );

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };

        let mut slabs_before = vec![empty_slab, partial_slab1, partial_slab2, full_slab];
        slabs_before.sort();
        let mut slabs_after = unsafe { cache_slabs(&raw mut cache) };
        slabs_after.sort();
        assert_eq!(
            slabs_before, slabs_after,
            "The `cache` should have the same slabs before and after"
        );

        let mut expected_allocated_objects = vec![
            slab_object.object.addr(),
            _slab_object1.object.addr(),
            _slab_object2.object.addr(),
            _slab_object3.object.addr(),
            _slab_object4.object.addr(),
        ];
        expected_allocated_objects.sort();
        let mut actual_allocated_objects = unsafe { cache_allocated_addrs(&raw mut cache) };
        actual_allocated_objects.sort();
        assert_eq!(
            expected_allocated_objects, actual_allocated_objects,
            "The `cache` should have the expected objects allocated"
        );
    }

    #[test]
    #[should_panic(expected = "Cache::deallocate_object: cache should not be null")]
    fn deallocate_object_from_null_cache_should_panic() {
        // Create a slab and allocate an object from it
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        let slab_object = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from header");

        // Exercise deallocate_object with null cache
        let _ = unsafe { Cache::deallocate_object(null_mut(), slab_object) };
    }

    #[test]
    #[should_panic(expected = "Cache::deallocate_object: object does not belong to the cache")]
    fn deallocate_object_from_other_cache_should_panic() {
        // Create a cache and an external slab that has an object allocated
        type T = TestObject;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        let slab_object = unsafe {
            SlabHeader::allocate_object(header).expect("Fail to allocate object from header")
        };

        // Exercise deallocate_object
        let _ = unsafe { Cache::deallocate_object(&raw mut cache, slab_object) };
    }

    #[test]
    fn deallocate_object_partial_slab_become_empty_and_slabs_partial_become_null() {
        // Create a cache that contains a single partial slab with an allocated object.
        type T = TestObject;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        let slab_object = unsafe {
            SlabHeader::allocate_object(only_slab)
                .expect("Failed to allocate object from only_slab")
        };
        cache.slabs_partial = only_slab;

        // Exercise deallocate_object and verify the result
        let result = unsafe { Cache::deallocate_object(&raw mut cache, slab_object) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        assert!(result.unwrap(), "The result should be true");

        // Verify the `cache`
        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            unsafe { cache_slabs(&raw mut cache) },
            "The cache should only contain the only_slab"
        );
        assert_eq!(
            0,
            unsafe { cache_allocated_addrs(&raw mut cache).len() },
            "The cache should have no object allocated"
        );
    }

    #[test]
    fn deallocate_object_full_slabs_become_partial_and_slabs_full_become_null() {
        // Create a cache that contains a full slab
        type T = TestObject;
        let mut cache = new_test_default::<T>();
        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let only_slab = slab_man.new_test_slab(&raw mut cache);
        assert_eq!(
            2,
            unsafe { (*only_slab).total_slots },
            "only_slab should have a total_slots of 2 for this test to work correctly"
        );
        let slab_object1 = unsafe {
            SlabHeader::allocate_object(only_slab)
                .expect("Failed to allocate object from only_slab")
        };
        let slab_object2 = unsafe {
            SlabHeader::allocate_object(only_slab)
                .expect("Failed to allocate object from only_slab")
        };
        cache.slabs_full = only_slab;

        // Exercise deallocate_object on slab_object1 and verify the result
        let result = unsafe { Cache::deallocate_object(&raw mut cache, slab_object1) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        assert!(result.unwrap(), "The result should be true");

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            vec![only_slab],
            unsafe { cache_slabs(&raw mut cache) },
            "The cache should only contain the only_slab"
        );
        assert_eq!(
            vec![slab_object2.object.addr()],
            unsafe { cache_allocated_addrs(&raw mut cache) },
            "The cache should only have the slab_object2 allocated"
        );
    }

    #[test]
    fn deallocate_object_partial_slab_and_remain_partial() {
        // Create a cache that contains two partial slabs.
        // One of them has two objects allocated.
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(3), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;

        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let slab1 = slab_man.new_test_slab(&raw mut cache);
        assert_eq!(
            3,
            unsafe { (*slab1).total_slots },
            "slab1 should have a total_slots of 2 for this test to work correctly"
        );
        let slab_object1 = unsafe {
            SlabHeader::allocate_object(slab1)
                .expect("Failed to allocate the first object from slab1")
        };
        let slab_object2 = unsafe {
            SlabHeader::allocate_object(slab1)
                .expect("Failed to allocate the second object from slab1")
        };

        let slab2 = slab_man.new_test_slab(&raw mut cache);
        let slab_object3 = unsafe {
            SlabHeader::allocate_object(slab2)
                .expect("Failed to allocate the first object from slab2")
        };

        unsafe {
            (*slab1).next = slab2;
            (*slab2).prev = slab1;
        }
        cache.slabs_partial = slab1;

        // Exercise deallocate_object on slab_object1 and verify the result
        let result = unsafe { Cache::deallocate_object(&raw mut cache, slab_object1) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        assert!(result.unwrap(), "The result should be true");

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };

        let mut expected_slabs = vec![slab1, slab2];
        expected_slabs.sort();
        let mut actual_slabs = unsafe { cache_slabs(&raw mut cache) };
        actual_slabs.sort();
        assert_eq!(
            expected_slabs, actual_slabs,
            "The `cache` should only contain the initial slabs",
        );

        let mut expected_allocated_addrs =
            vec![slab_object2.object.addr(), slab_object3.object.addr()];
        expected_allocated_addrs.sort();
        let mut actual_allocated_addrs = unsafe { cache_allocated_addrs(&raw mut cache) };
        actual_allocated_addrs.sort();
        assert_eq!(
            expected_allocated_addrs, actual_allocated_addrs,
            "The cache should only have the expected objects allocated"
        );
    }

    #[test]
    fn deallocate_object_full_slab_become_empty() {
        // Create a cache that contains two full slabs and one empty slab.
        // All slabs have a total_slots of one.
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut cache = new_test_default::<T>();
        cache.slab_layout = slab_layout;

        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let slab1 = slab_man.new_test_slab(&raw mut cache);
        assert_eq!(
            1,
            unsafe { (*slab1).total_slots },
            "slab1 should have a total_slots of 1 for this test to work correctly"
        );
        let slab_object1 = unsafe { SlabHeader::allocate_object(slab1) }
            .expect("Failed to allocate object from slab1");

        let slab2 = slab_man.new_test_slab(&raw mut cache);
        let slab_object2 = unsafe { SlabHeader::allocate_object(slab2) }
            .expect("Failed to allocate object from slab2");

        unsafe {
            (*slab1).next = slab2;
            (*slab2).prev = slab1;
        }
        cache.slabs_full = slab1;

        let slab3 = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = slab3;

        // Exercise deallocate_object on slab_object2 and verify the result
        let result = unsafe { Cache::deallocate_object(&raw mut cache, slab_object2) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        assert!(result.unwrap(), "The result should be true");

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };

        let mut expected_slabs = vec![slab1, slab2, slab3];
        expected_slabs.sort();
        let mut actual_slabs = unsafe { cache_slabs(&raw mut cache) };
        actual_slabs.sort();
        assert_eq!(
            expected_slabs, actual_slabs,
            "The cache should only contain the initial slabs"
        );

        let expected_allocated_addrs = vec![slab_object1.object.addr()];
        assert_eq!(
            expected_allocated_addrs,
            unsafe { cache_allocated_addrs(&raw mut cache) },
            "The cache should only have the expected objects allocated"
        );
    }

    #[test]
    #[should_panic(expected = "Cache::grow: addr0 should comply with the slab layout")]
    fn grow_when_addr0_violate_slab_alignment_should_panic() {
        // Create a cache that contains no slabs
        type T = TestObject;
        let mut cache = new_test_default::<T>();

        assert!(
            cache.slab_layout.align() > 1,
            "The slab layout should have an alignment greater than one for this test to work correctly"
        );

        // Exercise `grow` with a misaligned addr0
        let mut mem_block =
            Vec::<u8>::with_capacity(1 + cache.slab_layout.align() + cache.slab_layout.size());
        let addr0 = {
            let offset = mem_block.as_ptr().align_offset(cache.slab_layout.align());
            unsafe { mem_block.as_mut_ptr().add(offset + 1) }
        };
        let _ = unsafe { Cache::grow(&raw mut cache, NonNull::new_unchecked(addr0)) };
    }

    #[test]
    fn grow_succeeds_update_slabs_empty() {
        // Create a `cache` without any slabs
        type T = u64;
        let mut cache = new_test_default::<T>();

        let addrs = acquire_memory(cache.slab_layout, 10);
        let mut new_slabs = Vec::new();

        // The first `grow`
        {
            // Verify the result
            let result = unsafe { Cache::grow(&raw mut cache, NonNull::new_unchecked(addrs[0])) };
            assert!(
                result.is_ok(),
                "The result of the first grow should be Ok but got {result:?}"
            );
            let slab0 = result.unwrap();
            new_slabs.push(slab0);

            // Verify the `cache`
            unsafe { verify_cache_invariants(&raw mut cache) };
            new_slabs.sort();
            let mut slabs_after = unsafe { cache_slabs(&raw mut cache) };
            slabs_after.sort();
            assert_eq!(
                new_slabs, slabs_after,
                "`cache` should only contain the first grown slab"
            );
            assert_eq!(
                0,
                unsafe { cache_allocated_addrs(&raw mut cache).len() },
                "`cache` should have no object allocated"
            )
        }

        // The second `grow`
        {
            // Verify the result
            let result = unsafe { Cache::grow(&raw mut cache, NonNull::new_unchecked(addrs[1])) };
            assert!(
                result.is_ok(),
                "The result of the second grow should be Ok but got {result:?}"
            );
            let slab1 = result.unwrap();
            new_slabs.push(slab1);

            // Verify the `cache`
            unsafe { verify_cache_invariants(&raw mut cache) };
            new_slabs.sort();
            let mut slabs_after = unsafe { cache_slabs(&raw mut cache) };
            slabs_after.sort();
            assert_eq!(
                new_slabs, slabs_after,
                "`cache` should only contain the first two grown slabs"
            );
            assert_eq!(
                0,
                unsafe { cache_allocated_addrs(&raw mut cache).len() },
                "`cache` should have no object allocated"
            )
        }

        // The remaining `grow`s
        {
            for i in 2..addrs.len() {
                let result =
                    unsafe { Cache::grow(&raw mut cache, NonNull::new_unchecked(addrs[i])) };
                assert!(
                    result.is_ok(),
                    "The result of each remaining `grow` should be Ok but got {result:?}"
                );
                let slab = result.unwrap();
                new_slabs.push(slab);
            }

            // Verify the `cache`
            unsafe { verify_cache_invariants(&raw mut cache) };
            new_slabs.sort();
            let mut slabs_after = unsafe { cache_slabs(&raw mut cache) };
            slabs_after.sort();
            assert_eq!(
                new_slabs, slabs_after,
                "`cache` should only contain all the grown empty slabs"
            );
            assert_eq!(
                0,
                unsafe { cache_allocated_addrs(&raw mut cache).len() },
                "`cache` should have no object allocated"
            )
        }

        // Teardown
        drop(new_slabs);
        unsafe { release_memory(&addrs, cache.slab_layout) }
    }

    #[test]
    fn shrink_when_no_empty_slab_return_null_ptr() {
        // Create a cache that contains no slabs
        type T = TestObject;
        let mut cache = new_test_default::<T>();

        // Exercise shrink and verify the result
        let result = unsafe { Cache::shrink(&raw mut cache) };
        assert_eq!(
            null_mut(),
            result,
            "The result should be null but got {result:?}"
        );

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The cache should contain no slabs"
        )
    }

    #[test]
    fn shrink_when_single_empty_slab_then_slabs_empty_become_null() {
        // Create a cache that contains an empty slab and a partial slab.
        type T = TestObject;
        let mut cache = new_test_default();

        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);

        let slab1 = slab_man.new_test_slab(&raw mut cache);
        cache.slabs_empty = slab1;

        let slab2 = slab_man.new_test_slab(&raw mut cache);
        let slab_object = unsafe { SlabHeader::allocate_object(slab2) }
            .expect("Failed to allocate object from slab2");
        cache.slabs_partial = slab2;

        // Exercise shrink and verify the result
        let result = unsafe { Cache::shrink(&raw mut cache) };
        assert_eq!(slab1 as *mut u8, result, "The result should be the slab1");

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };

        assert_eq!(
            vec![slab2],
            unsafe { cache_slabs(&raw mut cache) },
            "The cache should only contain the slab2"
        );
        assert_eq!(
            vec![slab_object.object.addr()],
            unsafe { cache_allocated_addrs(&raw mut cache) },
            "The cache should only have slab_object allocated"
        );
    }

    #[test]
    fn shrink_when_multiple_empty_slabs_return_evicted_slab_ptr() {
        // Create a cache that contains two empty slabs
        type T = TestObject;
        let mut cache = new_test_default();

        let mut slab_man = SlabMan::<T>::new(cache.slab_layout);
        let slab1 = slab_man.new_test_slab(&raw mut cache);
        let slab2 = slab_man.new_test_slab(&raw mut cache);
        unsafe {
            (*slab1).next = slab2;
            (*slab2).prev = slab1;
        }
        cache.slabs_empty = slab1;

        // Exercise shrink and verify the result
        let result = unsafe { Cache::shrink(&raw mut cache) };
        assert!(
            result == slab1 as *mut u8 || result == slab2 as *mut u8,
            "The result should be either slab1 or slab2"
        );

        // Verify the cache
        unsafe { verify_cache_invariants(&raw mut cache) };

        let cache_slabs = unsafe { cache_slabs(&raw mut cache) };
        assert_eq!(
            1,
            cache_slabs.len(),
            "The cache should only contain one slab"
        );
        assert!(
            cache_slabs.contains(&slab1) || cache_slabs.contains(&slab2),
            "The cache should contain either slab1 or slab2"
        );
        assert_ne!(
            cache_slabs[0] as *mut u8, result,
            "The cache should not contain the evicted slab"
        );

        assert_eq!(
            0,
            unsafe { cache_allocated_addrs(&raw mut cache).len() },
            "The cache should have no object allocated"
        );
    }

    #[test]
    #[should_panic(expected = "Cache::new: zero size type is not supported")]
    fn new_when_zero_size_type_should_panic() {
        let slab_layout = Layout::from_size_align(0, 1024).expect("Failed to create slab_layout");
        let _ = Cache::<()>::new(['c'; CACHE_NAME_LENGTH], slab_layout);
    }

    #[test]
    #[should_panic(expected = "Cache::new: slab_layout is not properly aligned")]
    fn new_when_slab_layout_not_aligned_should_panic() {
        type T = TestObject;
        assert!(
            align_of::<SlabHeader<T>>() > 2,
            "The type should have an align greater than 2 for this test to work correctly"
        );

        let slab_layout = Layout::from_size_align(safe_slab_size::<T>(1), 2)
            .expect("Failed to create slab_layout");
        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], slab_layout);
    }

    #[test]
    #[should_panic(
        expected = "Cache::new: slab_layout should not smaller than Cache::min_slab_size"
    )]
    fn new_when_slab_layout_smaller_than_min_slab_size_should_panic() {
        type T = TestObject;
        let slab_layout = Layout::from_size_align(size_of::<T>(), align_of::<SlabHeader<T>>())
            .expect("Failed to create slab_layout");

        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], slab_layout);
    }

    #[test]
    fn new_when_valid_slab_layout_return_an_new_cache() {
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(Cache::<T>::min_slab_size(), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], slab_layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }
}

#[cfg(test)]
mod header_tests {
    extern crate alloc;

    use super::*;
    use crate::mem::slab::test_utils::{
        safe_slab_size, slab_allocated_addrs, verify_slab_invariants, SlabMan, TestObject,
    };
    use alloc::vec::Vec;
    use alloc::{format, vec};
    use core::any::type_name;
    use Error::NotAnObjectOfCurrentSlab;

    #[test]
    fn compute_slot0_offset_with_general_input() {
        let expected: ByteSize = 5;
        let addr0: usize = 0;
        let header_size: ByteSize = 5;
        assert_compute_slot0_offset::<u8>(expected, addr0, header_size);

        let expected: ByteSize = 23;
        let addr0: usize = 0x8000_fff1;
        let header_size: ByteSize = 16;
        assert_compute_slot0_offset::<u64>(expected, addr0, header_size);

        let expected: ByteSize = 31;
        let addr0: usize = 0x8000_fff1;
        let header_size: ByteSize = 22;
        assert_compute_slot0_offset::<u128>(expected, addr0, header_size);

        let expected: ByteSize = 31;
        let addr0: usize = 0x8000_fff1;
        let header_size: ByteSize = 28;
        assert_compute_slot0_offset::<u128>(expected, addr0, header_size);

        let expected: ByteSize = 30;
        let addr0: usize = 0x8000_fff2;
        let header_size: ByteSize = 28;
        assert_compute_slot0_offset::<u128>(expected, addr0, header_size);
    }

    fn assert_compute_slot0_offset<T: Default>(
        expected: ByteSize,
        addr0: usize,
        header_size: ByteSize,
    ) {
        let actual = SlabHeader::<T>::compute_slot0_offset(addr0, header_size);
        assert_eq!(
            expected,
            actual,
            "addr0= {addr0:?}, header_size= {header_size:?}, type= {:?}",
            type_name::<T>()
        );
    }

    #[test]
    fn first_free_slot_with_general_input() {
        assert_first_free_slot(&[0; SLAB_USED_BITMAP_SIZE], 0);
        assert_first_free_slot(&[0xffff_ffff_ffff_ffff; SLAB_USED_BITMAP_SIZE], 256);
        assert_first_free_slot(&[0xffff_ffff_ffff_ffef, 0, 0, 0], 4);
        assert_first_free_slot(
            &[
                0xffff_ffff_ffff_fffe,
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
            ],
            0,
        );
        assert_first_free_slot(
            &[
                0xffff_ffff_ffff_ffff,
                0xbe90_d505_a7b5_5fd3,
                0x3e68_6334_b578_70e0,
                0xda4b_62b9_3338_480c,
            ],
            66,
        );
        assert_first_free_slot(
            &[
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0x3e68_6334_b578_ffff,
                0xda4b_62b9_3338_480c,
            ],
            144,
        );
        assert_first_free_slot(
            &[
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0xda4b_62b9_ffff_ffff,
            ],
            225,
        );
        assert_first_free_slot(
            &[
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0x7fff_ffff_ffff_ffff,
            ],
            255,
        );
    }

    fn assert_first_free_slot(used_bitmap: &[u64; SLAB_USED_BITMAP_SIZE], expected: usize) {
        let actual = SlabHeader::<u8>::first_free_slot(used_bitmap);
        assert_eq!(expected, actual, "used_bitmap= {used_bitmap:x?}")
    }

    #[test]
    #[should_panic(expected = "`slot_index` should be less than the `MAX_SLOTS_PER_SLAB`")]
    fn alter_used_bit_with_index_equals_max_slots_per_slab_should_panic() {
        SlabHeader::<u8>::alter_used_bit(&mut [0; SLAB_USED_BITMAP_SIZE], MAX_SLOTS_PER_SLAB);
    }

    #[test]
    #[should_panic(expected = "`slot_index` should be less than the `MAX_SLOTS_PER_SLAB`")]
    fn alter_used_bit_with_index_greater_than_max_slots_per_slab_should_panic() {
        SlabHeader::<u8>::alter_used_bit(&mut [0; SLAB_USED_BITMAP_SIZE], MAX_SLOTS_PER_SLAB + 1);
    }

    #[test]
    fn alter_used_bit_with_valid_input() {
        assert_alter_used_bit(&mut [0, 0, 0, 0], 5, &mut [0x20, 0, 0, 0]);
        assert_alter_used_bit(&mut [0x20, 0, 0, 0], 5, &mut [0, 0, 0, 0]);
        assert_alter_used_bit(
            &mut [0xffff_ffff_ffff_ffff; SLAB_USED_BITMAP_SIZE],
            255,
            &mut [
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0x7fff_ffff_ffff_ffff,
            ],
        );
        assert_alter_used_bit(
            &mut [
                0xffff_ffff_ffff_ffff,
                0xbe90_d505_a7b5_5fd3,
                0x3e68_6334_b578_70e0,
                0xda4b_62b9_3338_480c,
            ],
            66,
            &mut [
                0xffff_ffff_ffff_ffff,
                0xbe90_d505_a7b5_5fd7,
                0x3e68_6334_b578_70e0,
                0xda4b_62b9_3338_480c,
            ],
        );
        assert_alter_used_bit(
            &mut [
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0x3e68_6334_b578_ffff,
                0xda4b_62b9_3338_480c,
            ],
            147,
            &mut [
                0xffff_ffff_ffff_ffff,
                0xffff_ffff_ffff_ffff,
                0x3e68_6334_b570_ffff,
                0xda4b_62b9_3338_480c,
            ],
        );
    }

    fn assert_alter_used_bit(
        used_bitmap: &mut [u64; SLAB_USED_BITMAP_SIZE],
        slot_index: usize,
        expected_after: &mut [u64; SLAB_USED_BITMAP_SIZE],
    ) {
        let before_str = format!("{:?}", used_bitmap);
        SlabHeader::<u8>::alter_used_bit(used_bitmap, slot_index);
        assert_eq!(
            expected_after, used_bitmap,
            "before= {before_str}, slot_index= {slot_index}"
        );
    }

    #[test]
    fn header_after_use_first_free_slot_should_have_valid_state() {
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(5), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::new(slab_layout);

        let test_slab = slab_man.new_test_slab(null_mut());
        for i in unsafe { 0..(*test_slab).total_slots } {
            let result = unsafe { SlabHeader::<T>::use_first_free_slot(test_slab) };
            assert!(
                result.is_ok(),
                "The result should be Ok but got {result:?} at the {i:?} call"
            );
            assert_eq!(
                i + 1,
                unsafe { (*test_slab).used_count },
                "The `used_count` should be {i:?} at the {i:?} call"
            );
            unsafe { verify_slab_invariants(test_slab, slab_layout.size()) };
        }
    }

    #[test]
    fn allocate_object_from_full_slab_should_return_err() {
        // Create a full slab
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::new(slab_layout);

        let full_slab = slab_man.new_test_slab(null_mut());
        let _ = unsafe { SlabHeader::<T>::use_first_free_slot(full_slab) };
        assert!(
            unsafe { SlabHeader::<T>::is_full(full_slab) },
            "`full_slab` should be full for the test to work correctly"
        );

        // Exercise `allocate_object` and verify the result
        let result = unsafe { SlabHeader::<T>::allocate_object(full_slab) };
        assert!(
            result.is_err(),
            "The result should be Err(AllocateFromFullSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, AllocateFromFullSlab),
            "The err should be {:?} but got {err:?}",
            AllocateFromNullSlab
        );

        // Verify the `full_slab`
        unsafe { verify_slab_invariants(full_slab, slab_layout.size()) };
        assert!(
            unsafe { SlabHeader::<T>::is_full(full_slab) },
            "The `full_slab` should remain full"
        );
    }

    #[test]
    fn allocate_object_success_should_return_object_with_default_value() {
        // Create an empty slab
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let slab = slab_man.new_test_slab(null_mut());

        // Exercise `allocate_object` and verify the result
        let result = unsafe { SlabHeader::<T>::allocate_object(slab) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let slab_object = result.unwrap();
        assert_eq!(
            &T::default(),
            slab_object.get_ref(),
            "The object behind the allocated [SlabObject] should have the default value"
        )
    }

    #[test]
    fn header_after_success_allocate_object_should_have_valid_state() {
        // Create an empty slab
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(5), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let slab = slab_man.new_test_slab(null_mut());

        // Exercise `allocate_object` and verify
        for i in unsafe { 0..(*slab).total_slots } {
            let result = unsafe { SlabHeader::<T>::allocate_object(slab) };
            assert!(result.is_ok(), "The result should be Ok but got {result:?}");
            assert_eq!(
                i + 1,
                unsafe { (*slab).used_count },
                "The `used_count` of `slab` should be {i:?} at the {i:?} call"
            );
            unsafe { verify_slab_invariants(slab, slab_layout.size()) };
        }
    }

    #[test]
    #[should_panic(expected = "SlabHeader::deallocate_object: header should not be null")]
    fn deallocate_object_from_null_header_should_panic() {
        // Create a slab and allocate an object from it
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        let slab_object = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");

        // Exercise `deallocate_object` with null header
        let _ = unsafe { SlabHeader::deallocate_object(null_mut(), slab_object) };
    }

    #[test]
    fn deallocate_object_from_different_header_return_wrong_slab_err() {
        // Create two slabs and allocate one object from each one of them
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let slab1 = slab_man.new_test_slab(null_mut());
        let _slab_object1 = unsafe { SlabHeader::allocate_object(slab1) }
            .expect("Failed to allocate object from `slab1`");

        let slab2 = slab_man.new_test_slab(null_mut());
        let slab_object2 = unsafe { SlabHeader::allocate_object(slab2) }
            .expect("Failed to allocate object from `slab2`");

        // Exercise `deallocate_object` from wrong slab and verify the result
        let result = unsafe { SlabHeader::deallocate_object(slab1, slab_object2) };
        assert!(
            result.is_err(),
            "The result should be Err(NotAnObjectOfCurrentSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, NotAnObjectOfCurrentSlab),
            "The err should be {:?} but got {err:?}",
            NotAnObjectOfCurrentSlab
        );
    }

    #[test]
    #[should_panic(expected = "SlabHeader::deallocate_object: deallocate from an unused slot")]
    fn deallocate_object_has_not_been_allocated_should_panic() {
        // Create an empty slab and craft a SlabObject pointing to an unused slot
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(1), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        let slab_object = SlabObject {
            source: header,
            object: unsafe { (*header).slot0.as_ptr() as *mut T },
            _marker: PhantomData,
        };

        // Exercise `deallocate_object`
        let _ = unsafe { SlabHeader::deallocate_object(header, slab_object) };
    }

    #[test]
    fn deallocate_object_from_single_allocation_slab() {
        // Create a slab and allocate an object from it
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        let slab_object = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");

        // Exercise `deallocate_object` and verify the result
        let result = unsafe { SlabHeader::deallocate_object(header, slab_object) };
        assert!(
            result.is_ok(),
            "The result should be Ok(true) but got {result:?}"
        );
        assert!(result.unwrap(), "The result should be true");

        // Verify the `header`
        unsafe { verify_slab_invariants(header, slab_layout.size()) };
        let allocated_addrs = unsafe { slab_allocated_addrs(header) };
        assert_eq!(
            0,
            allocated_addrs.len(),
            "The `header` should not have any object allocated but got {allocated_addrs:?}"
        );
    }

    #[test]
    fn deallocate_object_from_fully_allocated_slab_until_free() {
        // Create a slab and has all its slots allocated
        type T = TestObject;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(4), align_of::<SlabHeader<T>>())
                .expect("Failed to create `slab_layout`");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        let header = slab_man.new_test_slab(null_mut());
        assert_eq!(
            4,
            unsafe { (*header).total_slots },
            "The header should have a `total_slots` of 4 in order for this test to work correctly"
        );

        let slab_object0 = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");
        let slab_object1 = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");
        let slab_object2 = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");
        let slab_object3 = unsafe { SlabHeader::allocate_object(header) }
            .expect("Failed to allocate object from `header`");

        // Exercise `deallocate_object` until the slab is free
        let mut slab_objects = vec![slab_object2, slab_object3, slab_object0, slab_object1];
        while slab_objects.len() > 0 {
            let slab_object = slab_objects.pop().unwrap();
            // Verify the result
            let result = unsafe { SlabHeader::deallocate_object(header, slab_object) };
            assert!(
                result.is_ok(),
                "The result should be Ok(true) but got {result:?}"
            );
            assert!(result.unwrap(), "The result should be true");

            // Verify the `header`
            unsafe { verify_slab_invariants(header, slab_layout.size()) };

            let mut expected_allocated_addrs = slab_objects
                .iter()
                .map(|so| so.object.addr())
                .collect::<Vec<_>>();
            expected_allocated_addrs.sort();
            let mut actual_allocated_addrs = unsafe { slab_allocated_addrs(header) };
            actual_allocated_addrs.sort();
            assert_eq!(
                expected_allocated_addrs, actual_allocated_addrs,
                "The `header` should have the expected objects allocated"
            );
        }
    }

    #[test]
    fn object_slot_index_valid_input_return_index() {
        type T = TestObject;
        let slot0_addr = 0xa000_0000;
        let total_slots = MAX_SLOTS_PER_SLAB;
        let slot_size = size_of::<T>();

        let expected_indices = vec![0, 1, 55, 128, 166, MAX_SLOTS_PER_SLAB - 1];
        for &expected in expected_indices.iter() {
            let object_addr = slot0_addr + slot_size * expected;
            assert_eq!(
                Ok(expected),
                SlabHeader::<T>::object_slot_index(slot0_addr, slot_size, total_slots, object_addr),
                "slot0_addr= {slot0_addr}, slot_size= {slot_size}, object_addr= {object_addr}"
            );
        }
    }

    #[test]
    fn object_slot_index_object_addr_not_aligned_to_slots_return_err() {
        type T = TestObject;
        let slot0_addr = 0xa002_0000;
        let slot_size = size_of::<T>();
        let max_slots = MAX_SLOTS_PER_SLAB;
        assert_ne!(
            1, slot_size,
            "The `slot_size` should be greater than one for the test to work correctly"
        );
        let object_addr = slot0_addr + slot_size + 1;

        let result =
            SlabHeader::<T>::object_slot_index(slot0_addr, slot_size, max_slots, object_addr);
        assert!(
            result.is_err(),
            "The result should be Err(NotAnObjectOfCurrentSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, NotAnObjectOfCurrentSlab),
            "The error should be {:?} but got {err:?}",
            NotAnObjectOfCurrentSlab
        );
    }

    #[test]
    fn object_slot_index_object_before_slot0_return_err() {
        type T = TestObject;
        let slot0_addr = 0xa002_0000;
        let slot_size = size_of::<T>();
        let max_slots = MAX_SLOTS_PER_SLAB;
        let object_addr = slot0_addr - slot_size;

        let result =
            SlabHeader::<T>::object_slot_index(slot0_addr, slot_size, max_slots, object_addr);
        assert!(
            result.is_err(),
            "The result should be Err(NotAnObjectOfCurrentSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, NotAnObjectOfCurrentSlab),
            "The error should be {:?} but got {err:?}",
            NotAnObjectOfCurrentSlab
        );
    }

    #[test]
    fn object_slot_index_object_right_after_slab_boundary_return_err() {
        type T = TestObject;
        let slot0_addr = 0xa002_0000;
        let slot_size = size_of::<T>();
        let total_slots = 2;
        let object_addr = slot0_addr + slot_size * total_slots;

        let result =
            SlabHeader::<T>::object_slot_index(slot0_addr, slot_size, total_slots, object_addr);
        assert!(
            result.is_err(),
            "The result should be Err(NotAnObjectOfCurrentSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, NotAnObjectOfCurrentSlab),
            "The error should be {:?} but got {err:?}",
            NotAnObjectOfCurrentSlab
        );
    }

    #[test]
    fn object_slot_index_object_exceed_slab_boundary_return_err() {
        type T = TestObject;
        let slot0_addr = 0xa002_0000;
        let slot_size = size_of::<T>();
        let total_slots = 2;
        let object_addr = slot0_addr + slot_size * (total_slots + 1);

        let result =
            SlabHeader::<T>::object_slot_index(slot0_addr, slot_size, total_slots, object_addr);
        assert!(
            result.is_err(),
            "The result should be Err(NotAnObjectOfCurrentSlab) but got {result:?}"
        );
        let err = result.unwrap_err();
        assert!(
            matches!(err, NotAnObjectOfCurrentSlab),
            "The error should be {:?} but got {err:?}",
            NotAnObjectOfCurrentSlab
        );
    }

    #[test]
    #[should_panic(expected = "The `slot_index` is out of bounds")]
    fn is_slot_in_use_slot_index_equals_total_slots_should_panic() {
        let _ = SlabHeader::<u8>::is_slot_in_use(&[0; SLAB_USED_BITMAP_SIZE], 5, 5);
    }

    #[test]
    #[should_panic(expected = "The `slot_index` is out of bounds")]
    fn is_slot_in_use_slot_index_exceed_total_slots_should_panic() {
        let _ = SlabHeader::<u8>::is_slot_in_use(
            &[0; SLAB_USED_BITMAP_SIZE],
            MAX_SLOTS_PER_SLAB,
            MAX_SLOTS_PER_SLAB + 1,
        );
    }

    #[test]
    fn is_slot_in_use_used_slot_index_should_return_true() {
        type T = TestObject;
        let used_bitmap = [
            0x0000_0000_0000_9876,
            0xffff_ffff_ffff_ffff,
            0x0000_0000_fa00_cb00,
            0x0de0_a0f0_c0f0_0000,
        ];
        let used_slot_indices = vec![
            1, 2, 4, 5, 6, 11, 12, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78,
            79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
            100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
            117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 136, 137, 139, 142, 143, 153,
            155, 156, 157, 158, 159, 212, 213, 214, 215, 222, 223, 228, 229, 230, 231, 237, 239,
            245, 246, 247, 248, 250, 251,
        ];
        for slot_index in used_slot_indices {
            assert!(
                SlabHeader::<T>::is_slot_in_use(&used_bitmap, MAX_SLOTS_PER_SLAB, slot_index),
                "Slot {slot_index} should be in use: used_bitmap= {used_bitmap:?}"
            );
        }
    }

    #[test]
    fn is_slot_in_use_unused_index_should_return_false() {
        let used_bitmap = [
            0x6cf0_83e7_82ca_1bec,
            0x2d24_6b8c_8721_1c2c,
            0x1a39_49c9_bcdc_654d,
            0xa2d0_6280_e029_35e0,
        ];
        let unused_slot_indices = vec![
            0, 1, 4, 10, 13, 14, 15, 16, 18, 20, 21, 24, 26, 27, 28, 29, 30, 35, 36, 42, 43, 44,
            45, 46, 48, 49, 50, 51, 56, 57, 60, 63, 64, 65, 68, 70, 71, 72, 73, 77, 78, 79, 81, 82,
            83, 84, 86, 87, 91, 92, 93, 94, 96, 97, 100, 101, 102, 106, 108, 111, 112, 113, 115,
            116, 118, 119, 121, 124, 126, 127, 129, 132, 133, 135, 137, 139, 140, 143, 144, 145,
            149, 152, 153, 158, 161, 162, 164, 165, 169, 170, 172, 173, 175, 177, 178, 182, 183,
            184, 186, 189, 190, 191, 192, 193, 194, 195, 196, 201, 203, 206, 207, 209, 210, 212,
            214, 215, 216, 217, 218, 219, 220, 224, 225, 226, 227, 228, 229, 230, 232, 234, 235,
            236, 239, 240, 241, 242, 243, 245, 248, 250, 251, 252, 254,
        ];

        for slot_index in unused_slot_indices {
            assert!(
                !SlabHeader::<u8>::is_slot_in_use(&used_bitmap, MAX_SLOTS_PER_SLAB, slot_index),
                "Slot {slot_index} should be unused: used_bitmap= {used_bitmap:?}"
            );
        }
    }
}

#[cfg(test)]
mod test_utils {
    extern crate alloc;
    use super::*;
    use alloc::alloc::{alloc, dealloc};
    use alloc::vec::Vec;
    use core::alloc::Layout;
    use core::ptr::{null_mut, NonNull};

    #[derive(Debug, PartialEq)]
    pub struct TestObject {
        x: u64,
        y: u32,
        z: usize,
    }

    impl Default for TestObject {
        fn default() -> Self {
            Self {
                x: 256,
                y: 128,
                z: 1024,
            }
        }
    }

    /// Calls `alloc` with the `layout` `count` times and
    /// returns a collection of the returned pointers.
    pub fn acquire_memory(layout: Layout, count: usize) -> Vec<*mut u8> {
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
    pub unsafe fn release_memory(ptrs: &[*mut u8], layout: Layout) {
        for &ptr in ptrs {
            unsafe { dealloc(ptr, layout) };
        }
    }

    /// Returns the size of the list starting from `head`.
    ///
    /// # SAFETY:
    /// * `head` must be a valid pointer.
    pub unsafe fn size_of_list<T: Default>(head: *mut SlabHeader<T>) -> usize {
        let mut result = 0;
        let mut curr = head;
        while !curr.is_null() {
            result += 1;
            curr = unsafe { (*curr).next };
        }
        result
    }

    /// Returns whether the list starting from `head` contains `node`.
    ///
    /// # SAFETY:
    /// * `head` must be a valid pointer.
    /// * `node` must be a valid pointer.
    pub unsafe fn contains_node<T: Default>(
        head: *mut SlabHeader<T>,
        node: *mut SlabHeader<T>,
    ) -> bool {
        let mut curr = head;
        while !curr.is_null() && curr != node {
            curr = unsafe { (*curr).next };
        }
        !curr.is_null()
    }

    /// Asserts whether the `head` represents a doubly linked list.
    ///
    /// # SAFETY:
    /// * `head` must be a valid pointer.
    pub unsafe fn verify_list_doubly_linked<T: Default>(head: *mut SlabHeader<T>) {
        assert_ne!(null_mut(), head, "`head` should not be null");
        assert_eq!(null_mut(), (*head).prev, "`prev` of `head` should be null");

        let mut curr = head;
        let mut next = (*curr).next;
        while !next.is_null() {
            assert_eq!(curr, (*next).prev, "`prev` of {next:?} should be {curr:?}");
            curr = next;
            next = (*curr).next;
        }
    }

    /// `verify_node_isolated` checks whether the `node` is isolated.
    ///
    /// # SAFETY:
    /// * `node` must be a valid pointer.
    pub unsafe fn verify_node_isolated<T: Default>(node: *mut SlabHeader<T>) {
        assert_eq!(
            null_mut(),
            (*node).prev,
            "`node` is not isolated: it has its `prev` linked"
        );
        assert_eq!(
            null_mut(),
            (*node).next,
            "`node` is not isolated: it has its `next` linked"
        );
    }

    pub struct SlabMan<T: Default> {
        slab_layout: Layout,
        allocated: Vec<*mut u8>,
        _type_marker: PhantomData<T>,
    }

    impl<T: Default> SlabMan<T> {
        pub fn new(slab_layout: Layout) -> Self {
            assert_ne!(
                0,
                slab_layout.size(),
                "`slab_layout` size should not be zero"
            );
            assert_eq!(
                0,
                slab_layout.align() % align_of::<SlabHeader<T>>(),
                "`slab_layout` should align to the alignment of SlabHeader<T>"
            );

            Self {
                slab_layout,
                allocated: Vec::new(),
                _type_marker: PhantomData,
            }
        }

        /// `new_test_slab` returns a pointer to the newly allocated test slab.
        pub fn new_test_slab(&mut self, cache: *mut Cache<T>) -> *mut SlabHeader<T> {
            let addr0 = unsafe { alloc(self.slab_layout) };
            assert_ne!(null_mut(), addr0, "Failed to allocate memory");
            self.allocated.push(addr0);

            unsafe {
                SlabHeader::<T>::new(
                    cache,
                    self.slab_layout.size(),
                    NonNull::new_unchecked(addr0),
                )
            }
        }
    }

    impl<T: Default> Drop for SlabMan<T> {
        fn drop(&mut self) {
            unsafe { release_memory(&self.allocated, self.slab_layout) }
        }
    }

    /// `safe_slab_size` assumes the slot size is equal to the size of `T` and
    /// returns a slab size that can accommodate `total_slots`.
    pub fn safe_slab_size<T: Default>(total_slots: usize) -> ByteSize {
        size_of::<SlabHeader<T>>() + align_of::<T>() + size_of::<T>() * total_slots
    }

    /// Verify if the `cache` satisfies the invariants of a [Cache].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    pub unsafe fn verify_cache_invariants<T: Default>(cache: *mut Cache<T>) {
        verify_cache_type(cache);
        verify_cache_slab_layout(cache);
        verify_cache_slabs_full(cache);
        verify_cache_slabs_partial(cache);
        verify_cache_slabs_empty(cache);
    }

    /// Verify if the type [T] of `cache` satisfies the invariant of a [Cache].
    ///
    /// SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_cache_type<T: Default>(_cache: *mut Cache<T>) {
        assert_ne!(0, size_of::<T>(), "Zero-size type not supported");
    }

    /// Verify if the `slab_layout` of `cache` satisfies the invariant of a [Cache].
    ///
    /// SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_cache_slab_layout<T: Default>(cache: *mut Cache<T>) {
        assert!(
            size_of::<T>() + size_of::<SlabHeader<T>>() <= (*cache).slab_layout.size(),
            "The size of `slab_layout` is too small"
        );
        assert_eq!(
            0,
            (*cache).slab_layout.align() % align_of::<SlabHeader<T>>(),
            "The alignment of `slab_layout` is incompatible with SlabHeader<T>"
        );
    }

    /// Verify if the `slabs_full` satisfies the invariants of a [Cache].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_cache_slabs_full<T: Default>(cache: *mut Cache<T>) {
        if (*cache).slabs_full.is_null() {
            return;
        }
        let list = (*cache).slabs_full;
        verify_list_doubly_linked(list);
        verify_list_slabs_source(list, cache);
        verify_list_slabs_all_full(list);
        verify_list_slabs_invariants(list, (*cache).slab_layout.size());
    }

    /// Verify if all the slabs in this `list` belong to `source`.
    ///
    /// # SAFETY:
    /// * `list` must be a valid pointer.
    /// * `source` must be a valid pointer.
    unsafe fn verify_list_slabs_source<T: Default>(
        head: *mut SlabHeader<T>,
        source: *mut Cache<T>,
    ) {
        let mut curr = head;
        while !curr.is_null() {
            assert_eq!(
                source,
                (*curr).source,
                "Slabs in this `list` should belong to the `source`"
            );
            curr = (*curr).next
        }
    }

    /// Verify if all the slabs in this list are full.
    ///
    /// # SAFETY:
    /// * `head` must be a valid pointer.
    unsafe fn verify_list_slabs_all_full<T: Default>(head: *mut SlabHeader<T>) {
        let mut curr = head;
        while !curr.is_null() {
            assert_eq!(
                (*curr).total_slots,
                (*curr).used_count,
                "Slabs in this `list` should be full"
            );
            curr = (*curr).next;
        }
    }

    /// Verify if all the slabs in this `list` satisfy the invariants of a [SlabHeader].
    ///
    /// # SAFETY:
    /// * `list` must be a valid pointer.
    unsafe fn verify_list_slabs_invariants<T: Default>(
        head: *mut SlabHeader<T>,
        slab_size: ByteSize,
    ) {
        let mut curr = head;
        while !curr.is_null() {
            verify_slab_invariants(curr, slab_size);
            curr = (*curr).next;
        }
    }

    /// Verify if the `slabs_partial` satisfies the invariants of a [Cache].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_cache_slabs_partial<T: Default>(cache: *mut Cache<T>) {
        if (*cache).slabs_partial.is_null() {
            return;
        }
        let list = (*cache).slabs_partial;
        verify_list_doubly_linked(list);
        verify_list_slabs_source(list, cache);
        verify_list_slabs_all_partial_full(list);
        verify_list_slabs_invariants(list, (*cache).slab_layout.size());
    }

    /// Verify if all the slabs in this `list` are partially full.
    ///
    /// # SAFETY:
    /// * `list` must be a valid pointer.
    unsafe fn verify_list_slabs_all_partial_full<T: Default>(head: *mut SlabHeader<T>) {
        let mut curr = head;
        while !curr.is_null() {
            assert!(
                0 < (*curr).used_count && (*curr).used_count < (*curr).total_slots,
                "Slabs in this `list` should be partially full"
            );
            curr = (*curr).next;
        }
    }

    /// Verify if the `slabs_empty` satisfies the invariants of a [Cache].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_cache_slabs_empty<T: Default>(cache: *mut Cache<T>) {
        if (*cache).slabs_empty.is_null() {
            return;
        }
        let list = (*cache).slabs_empty;
        verify_list_doubly_linked(list);
        verify_list_slabs_source(list, cache);
        verify_list_slabs_all_empty(list);
        verify_list_slabs_invariants(list, (*cache).slab_layout.size());
    }

    /// Verify if all the slabs in this `list` are empty.
    ///
    /// # SAFETY:
    /// * `list` must be a valid pointer.
    unsafe fn verify_list_slabs_all_empty<T: Default>(head: *mut SlabHeader<T>) {
        let mut curr = head;
        while !curr.is_null() {
            assert_eq!(
                0,
                (*curr).used_count,
                "Slabs in this `list` should be empty"
            );
            curr = (*curr).next;
        }
    }

    /// # SAFETY:
    /// * `header` must be a valid pointer.
    pub unsafe fn verify_slab_invariants<T: Default>(
        header: *mut SlabHeader<T>,
        slab_size: ByteSize,
    ) {
        verify_slab_type(header);
        verify_slab_slot_attributes(header, slab_size);
        verify_slab_used_attributes(header);
    }

    /// Verify if the type [T] of `header` satisfies the invariant of a slab.
    ///
    /// SAFETY:
    /// * `cache` must be a valid pointer.
    unsafe fn verify_slab_type<T: Default>(_header: *mut SlabHeader<T>) {
        assert_ne!(0, size_of::<T>(), "Zero-size type not supported");
    }

    /// Verify if the slot attributes satisfy the invariants of a slab.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn verify_slab_slot_attributes<T: Default>(
        header: *mut SlabHeader<T>,
        slab_size: ByteSize,
    ) {
        assert!(
            0 < (*header).total_slots && (*header).total_slots <= MAX_SLOTS_PER_SLAB,
            "`total_slots` should be at least zero and not greater than the `MAX_SLOTS_PER_SLAB`"
        );
        assert_eq!(
            0,
            (*header).slot0.align_offset(align_of::<T>()),
            "`slot0` should align with the alignment of object [T]"
        );
        assert!(
            size_of::<T>() <= (*header).slot_size,
            "`slot_size` should be at least the size of object [T]"
        );
        assert_eq!(
            0,
            (*header).slot_size % align_of::<T>(),
            "`slot_size` should be a multiple of the alignment of object [T]"
        );
        assert!(
            (*header).slot0.addr().get() + (*header).slot_size * (*header).total_slots
                <= header.addr() + slab_size,
            "The last slot should not exceed the boundary of the slab"
        );
    }

    /// Verify if the used attributes satisfy the invariants of a slab.
    ///
    /// # SAFETY:
    /// * `header` must be a valid pointer.
    unsafe fn verify_slab_used_attributes<T: Default>(header: *mut SlabHeader<T>) {
        assert!(
            (*header).used_count <= (*header).total_slots,
            "`used_count` should not exceed `total_slots`"
        );

        assert_eq!(
            SLAB_USED_BITMAP_SIZE,
            (*header).used_bitmap.len(),
            "`used_bitmap` should have a size of the `SLAB_USED_BITMAP_SIZE`"
        );

        let set_bits_after_last_slot = ((*header).total_slots..MAX_SLOTS_PER_SLAB)
            .filter(|&slot| {
                let (index, shift) = (slot / 64, slot % 64);
                (*header).used_bitmap[index] & (1 << shift) != 0
            })
            .count();
        assert_eq!(
            0, set_bits_after_last_slot,
            "The bits in `used_bitmap` after the last slot should not be set"
        );

        let total_set_bits = (*header)
            .used_bitmap
            .iter()
            .map(|&bits| bits.count_ones() as usize)
            .sum();
        assert_eq!(
            (*header).used_count,
            total_set_bits,
            "`used_count` should match the total set bits in `used_bitmap`"
        )
    }

    /// `cache_allocated_addrs` collects the address of the objects allocated from this `cache`.
    ///
    /// # SAFETY:
    /// * `cache` must be either null or a valid pointer.
    pub unsafe fn cache_allocated_addrs<T: Default>(cache: *mut Cache<T>) -> Vec<usize> {
        if cache.is_null() {
            return Vec::new();
        }
        let mut result = Vec::new();
        result.append(&mut list_allocated_addrs((*cache).slabs_full));
        result.append(&mut list_allocated_addrs((*cache).slabs_partial));
        result.append(&mut list_allocated_addrs((*cache).slabs_empty));
        result
    }

    /// `list_allocated_addrs` collects the addresses of the objects allocated from the `head` list.
    ///
    /// # SAFETY:
    /// * `head` must be either null or a valid pointer.
    pub unsafe fn list_allocated_addrs<T: Default>(head: *mut SlabHeader<T>) -> Vec<usize> {
        let mut result = Vec::new();
        let mut curr = head;
        while !curr.is_null() {
            result.append(&mut slab_allocated_addrs(curr));
            curr = (*curr).next;
        }
        result
    }

    /// `slab_allocated_addrs` collects the addresses of the objects allocated from this `header`.
    ///
    /// # SAFETY:
    /// `header` must be either null or a valid pointer.
    pub unsafe fn slab_allocated_addrs<T: Default>(header: *mut SlabHeader<T>) -> Vec<usize> {
        if header.is_null() {
            return Vec::new();
        }

        (0..(*header).total_slots)
            .filter(|&i| {
                let (index, shift) = (i / 64, i % 64);
                (*header).used_bitmap[index] & (1 << shift) > 0
            })
            .map(|i| (*header).slot0.addr().get() + (*header).slot_size * i)
            .collect()
    }

    /// `cache_slabs` returns a list containing the slabs that belong to this `cache`.
    ///
    /// # SAFETY:
    /// * `cache` must be either null or a valid pointer.
    pub unsafe fn cache_slabs<T: Default>(cache: *mut Cache<T>) -> Vec<*mut SlabHeader<T>> {
        if cache.is_null() {
            return Vec::new();
        }
        let mut result = Vec::new();
        result.append(&mut list_slabs((*cache).slabs_full));
        result.append(&mut list_slabs((*cache).slabs_partial));
        result.append(&mut list_slabs((*cache).slabs_empty));
        result
    }

    /// `list_slabs` returns a list containing the slabs that belong to the `head` list.
    ///
    /// The slabs on the `prev` side of the `head` are ignored.
    ///
    /// # SAFETY:
    /// * `head` must be either null or a valid pointer.
    pub unsafe fn list_slabs<T: Default>(head: *mut SlabHeader<T>) -> Vec<*mut SlabHeader<T>> {
        let mut result = Vec::new();
        if head.is_null() {
            return result;
        }

        let mut curr = head;
        while !curr.is_null() {
            result.push(curr);
            curr = (*curr).next;
        }
        result
    }
}
