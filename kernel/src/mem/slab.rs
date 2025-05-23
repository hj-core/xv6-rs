// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

#![allow(unsafe_op_in_unsafe_fn)]

use crate::mem::slab::Error::NoSlabAvailable;
use Error::{AllocateFromFullSlab, AllocateFromNullSlab, NotAnObjectOfCurrentSlab};
use core::alloc::Layout;
use core::marker::PhantomData;
use core::marker::PhantomPinned;
use core::ptr;
use core::ptr::{NonNull, null_mut};

type ByteSize = usize;

const CACHE_NAME_LENGTH: usize = 16;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_SLOTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

/// [Cache] manages a collection of memory slabs (contiguous blocks of memory divided into
/// fixed-size slots), providing an interface for allocating and deallocating objects of type [T].
/// Clients can use the [Cache] to efficiently allocate new objects and return them
/// to the cache when they are no longer needed.
///
/// The `name` field is used for debugging and identification purposes.
///
/// Methods of [Cache] are not thread-safe; clients must provide proper synchronization
/// measures to protect the [Cache] from concurrent access.
///
/// The `#[repr(C)]` attribute ensures that the [Cache] struct has a well-defined memory
/// layout, which is important for potential interoperability with C code or when
/// relying on specific memory offsets.
///
/// # Safety:
/// * [Cache] is address-sensitive. Clients must ensure it is not moved after creation.
/// * [T] must not be `#[repr(packed)]`. Packed types can lead to undefined behavior when
///   accessed through pointers with alignment requirements.
/// * [T] must not be a zero-sized type. Zero-sized types are not supported by this
///   slab allocator.
#[repr(C)]
struct Cache<T>
where
    T: Default,
{
    /// The `name` field is used for debugging and identification purposes.
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
    /// The `name` is used for debugging and identification purposes.
    /// The `slab_layout` must have a size no less than [Cache::min_slab_size]
    /// and its alignment must be a multiple of [Cache::align_of_slab].
    ///
    /// # Panics
    ///
    /// This function will panic if:
    /// * [T] is a zero-sized type.
    /// * `slab_layout` is not properly aligned.
    /// * `slab_layout` is smaller than [Cache::min_slab_size].
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

    /// `allocate_object` attempts to allocate an object from the `cache`.
    ///
    /// It returns a [SlabObject] wrapping the allocated object if the allocation succeeds, or
    /// returns the corresponding [Error] if it fails. The allocated object has the default value
    /// of [T], and clients can access it through the [SlabObject].
    ///
    /// It is guaranteed that if an [Error] is returned, the `cache` remains unmodified.
    ///
    /// # Safety
    /// * The `cache` must be a valid pointer and in a valid state.
    ///
    /// # Panics
    /// This function panics if:
    /// * The `cache` is null.
    /// * Any of the slab list heads has its `prev` linked.
    unsafe fn allocate_object(cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        assert!(
            !cache.is_null(),
            "Cache::allocate_object: cache should not be null"
        );
        assert!(
            (*cache).slabs_full.is_null() || (*(*cache).slabs_full).prev.is_null(),
            "Cache::allocate_object: slabs_full should not have its prev linked"
        );
        assert!(
            (*cache).slabs_partial.is_null() || (*(*cache).slabs_partial).prev.is_null(),
            "Cache::allocate_object: slabs_partial should not have its prev linked"
        );
        assert!(
            (*cache).slabs_empty.is_null() || (*(*cache).slabs_empty).prev.is_null(),
            "Cache::allocate_object: slabs_empty should not have its prev linked"
        );

        if !(*cache).slabs_partial.is_null() {
            Self::allocate_from_partial(cache)
        } else if !(*cache).slabs_empty.is_null() {
            Self::allocate_from_empty(cache)
        } else {
            Err(NoSlabAvailable)
        }
    }

    /// `allocate_from_empty` attempts to allocate an object from one of the empty slabs.
    ///
    /// It returns a [SlabObject] wrapping the allocated object if the attempt succeeds, or returns
    /// the corresponding [Error] if it fails. The allocated object has the default value of [T],
    /// and clients can access it through the [SlabObject].
    ///
    /// It is guaranteed that if an [Error] is returned, the state of the `cache` remain unmodified.
    ///
    /// # Safety
    /// * `cache` must be a valid pointer and in a valid state.
    /// * `cache` must contain at least one empty slab.
    unsafe fn allocate_from_empty(cache: *mut Cache<T>) -> Result<SlabObject<T>, Error> {
        let result = SlabHeader::allocate_object((*cache).slabs_empty);
        if result.is_err() {
            return result;
        }

        // Update list heads
        let (moved_slab, new_head_empty) = Cache::pop_front((*cache).slabs_empty);
        (*cache).slabs_empty = new_head_empty;

        if SlabHeader::is_full(moved_slab) {
            (*cache).slabs_full = Cache::push_front((*cache).slabs_full, moved_slab);
        } else {
            (*cache).slabs_partial = Cache::push_front((*cache).slabs_partial, moved_slab);
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
        result
    }

    /// `push_front` pushes the `node` to the front of the doubly-linked list `head` and
    /// returns the new head.
    ///
    /// # SAFETY:
    /// * `head` should be either null or a valid pointer that doesn't have its `prev` linked.
    /// * `node` should be a valid pointer and isolated, i.e., not linked to other nodes.
    unsafe fn push_front(head: *mut SlabHeader<T>, node: *mut SlabHeader<T>) -> *mut SlabHeader<T> {
        if node.is_null() {
            panic!("Cache::push_front: node should not be null")
        }
        assert_eq!(
            null_mut(),
            (*node).prev,
            "Cache::push_front: node should not have its prev linked"
        );
        assert_eq!(
            null_mut(),
            (*node).next,
            "Cache::push_front: node should not have its next linked"
        );

        if head.is_null() {
            return node;
        };
        assert_eq!(
            null_mut(),
            (*head).prev,
            "Cache::push_front: head should not have its prev linked"
        );

        (*node).next = head;
        (*head).prev = node;
        node
    }

    /// `pop_front` detaches the first node from the doubly-linked list `head` and
    /// returns the detached node along with the new head.
    ///
    /// # SAFETY:
    /// * `head` should be a valid pointer.
    /// * `head` should not have its `prev` linked.
    unsafe fn pop_front(head: *mut SlabHeader<T>) -> (*mut SlabHeader<T>, *mut SlabHeader<T>) {
        assert!(!head.is_null(), "Cache::pop_front: head should not be null");

        assert_eq!(
            null_mut(),
            (*head).prev,
            "Cache::pop_front: head should not have its prev linked"
        );

        let new_head = (*head).next;
        if !new_head.is_null() {
            (*new_head).prev = null_mut();
            (*head).next = null_mut();
        }

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

        if SlabHeader::is_empty(header) {
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
    /// `new` attempts to create a slab for `cache` at `addr0` with a size of `slab_size`.
    /// It returns a pointer to the [SlabHeader].
    ///
    /// # SAFETY:
    /// * `slab_size` must be able to accommodate the [SlabHeader] and at least one [T],
    ///   with the alignment of [T] considered, i.e., padding after the [SlabHeader] to
    ///   comply with the alignment of [T].
    /// * `addr0` must be a valid pointer.
    /// * `addr0` must comply with the alignment of [SlabHeader].
    /// * The memory block starting at `addr0` and extending for `slab_size` must be dedicated
    ///   to the new slab's use.
    unsafe fn new(cache: *mut Cache<T>, slab_size: ByteSize, addr0: NonNull<u8>) -> *mut Self {
        let header_size: ByteSize = size_of::<SlabHeader<T>>();
        let slot_size: ByteSize = size_of::<T>();
        let slot0_offset = Self::compute_slot0_offset(addr0.addr().get(), header_size);
        let total_slots = (slab_size - slot0_offset) / slot_size;

        assert!(
            slot0_offset <= isize::MAX as usize,
            "slot0_offset must fit in an isize to satisfy the safety of NonNull::add"
        );

        // SAFETY:
        // We are safe to call add because:
        // * addr0 is a valid pointer.
        // * The computed offset, slot0_offset * size_of::<u8> cannot overflow isize.
        // * The computed offset is in bounds of addr0 because addr0 is backed by
        //   a memory block of slab_size, and slot0 is within the slab.
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
        // SAFETY:
        // We are safe to write the header to the result because
        // * addr0 is valid for writes.
        // * addr0 is properly aligned.
        // * The memory block is dedicated to the slab's use.
        unsafe { result.write(header) };

        result
    }

    /// `compute_slot0_offset` returns the offset from the [SlabHeader]'s address to slot 0.
    /// This offset considers the alignment requirements of object [T].
    ///
    /// If the header end overflows, it returns the expected offset.
    /// However, it will panic if the computed offset overflows.
    fn compute_slot0_offset(addr0: usize, header_size: ByteSize) -> ByteSize {
        let object_align = align_of::<T>();
        let rem = (addr0 % object_align + header_size % object_align) % object_align;
        let padding: ByteSize = if rem == 0 { 0 } else { object_align - rem };
        if header_size > usize::MAX - padding {
            panic!("SlabHeader::compute_slot0_offset: result overflow");
        }
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

    /// `is_empty` returns whether the underlying slab is empty.
    ///
    /// # SAFETY
    /// * `header` must be a valid pointer.
    unsafe fn is_empty(header: *mut SlabHeader<T>) -> bool {
        (*header).used_count == 0
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
    NoSlabAvailable,
    AllocateFromFullSlab,
    AllocateFromNullSlab,
    NotAnObjectOfCurrentSlab,
}

#[cfg(test)]
#[macro_use]
mod test_marcos {
    /// `test_panic_against_types` generates the "should_panic" tests against the given types
    /// for a generic test method.
    ///
    /// # Example
    /// ```//noinspection
    /// test_panic_against_types!(
    ///     my_generic_test_method,
    ///     the_expected_panic_message,
    ///     (name_for_the_generated_test_for_type1, Type1),
    ///     (name_for_the_generated_test_for_type2, Type2),
    ///     (name_for_the_generated_test_for_type3, Type3),
    /// );
    /// ```
    macro_rules! test_panic_against_types {
        ($test:ident, $panic_msg:literal, $(($fn_name:tt, $t:ty)), +,) => {
            $(
                #[test]
                #[should_panic(expected = $panic_msg)]
                fn $fn_name() {
                    $test::<$t>()
                }

            )+
        };
    }

    /// `test_against_types` generates the tests against the given types for a generic test method.
    ///
    /// # Example
    /// ```//noinspection
    /// test_against_types!(
    ///     my_generic_test_method,
    ///     (name_for_the_generated_test_for_type1, Type1),
    ///     (name_for_the_generated_test_for_type2, Type2),
    ///     (name_for_the_generated_test_for_type3, Type3),
    /// );
    /// ```
    macro_rules! test_against_types {
        ($test:ident, $(($fn_name:tt, $t:ty)), +,) => {
            $(
                #[test]
                fn $fn_name() {
                    $test::<$t>()
                }

            )+
        };
    }

    /// `test_against_types_arguments` generates the tests against the given types and arguments
    /// for a generic test method.
    ///
    /// # Example
    /// ```//noinspection
    /// test_against_types_arguments!(
    ///     my_generic_test_method,
    ///     (name_for_the_generated_test1, Type1, arg1, arg2),
    ///     (name_for_the_generated_test2, Type2, arg1, arg2),
    ///     (name_for_the_generated_test3, Type3, arg1, arg2),
    /// );
    /// ```
    macro_rules! test_against_types_arguments {
        ($test:ident, $(($fn_name:tt, $t:ty, $($args:expr), *)), +,) => {
            $(
                #[test]
                fn $fn_name() {
                    $test::<$t>($($args), *);
                }
            )+
        };
    }
}

#[cfg(test)]
mod cache_new_test {
    use crate::mem::slab::test_utils::{
        TestObject, cache_slabs, safe_slab_size, verify_cache_invariants,
    };
    use crate::mem::slab::{CACHE_NAME_LENGTH, Cache, SlabHeader};
    use core::alloc::Layout;

    #[test]
    #[should_panic(expected = "Cache::new: zero size type is not supported")]
    fn zero_size_type_panics() {
        let layout = Layout::from_size_align(16, 8).expect("Failed to create the layout");
        let _ = Cache::<()>::new(['c'; CACHE_NAME_LENGTH], layout);
    }

    #[test]
    #[should_panic(expected = "Cache::new: slab_layout is not properly aligned")]
    fn layout_not_aligned_with_header_panics_case_2() {
        type T = TestObject;
        assert!(
            align_of::<SlabHeader<T>>() > 2,
            "The type should have an align greater than 2 for this test to work correctly"
        );

        let layout = Layout::from_size_align(safe_slab_size::<T>(1), 2)
            .expect("Failed to create the layout");
        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);
    }

    #[test]
    #[should_panic(expected = "Cache::new: slab_layout is not properly aligned")]
    fn layout_not_aligned_with_header_panics_case_4() {
        type T = TestObject;
        assert!(
            align_of::<SlabHeader<T>>() > 4,
            "The type should have an align greater than 4 for this test to work correctly"
        );

        let layout = Layout::from_size_align(safe_slab_size::<T>(1), 4)
            .expect("Failed to create the layout");
        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);
    }

    #[test]
    #[should_panic(
        expected = "Cache::new: slab_layout should not smaller than Cache::min_slab_size"
    )]
    fn layout_smaller_than_min_slab_size_panics_case_test_object() {
        type T = TestObject;
        let layout = Layout::from_size_align(size_of::<T>(), align_of::<SlabHeader<T>>())
            .expect("Failed to create the layout");

        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);
    }

    #[test]
    #[should_panic(
        expected = "Cache::new: slab_layout should not smaller than Cache::min_slab_size"
    )]
    fn layout_smaller_than_min_slab_size_panics_case_u128() {
        type T = u128;
        let layout =
            Layout::from_size_align(size_of::<SlabHeader<T>>(), align_of::<SlabHeader<T>>())
                .expect("Failed to create the layout");

        let _ = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);
    }

    #[test]
    fn header_align_min_slab_size_returns_new_cache_case_test_object() {
        type T = TestObject;
        let layout =
            Layout::from_size_align(Cache::<T>::min_slab_size(), align_of::<SlabHeader<T>>())
                .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }

    #[test]
    fn header_align_min_size_returns_new_cache_case_u8() {
        type T = u8;
        let layout =
            Layout::from_size_align(Cache::<T>::min_slab_size(), align_of::<SlabHeader<T>>())
                .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }

    #[test]
    fn header_align_general_size_returns_new_cache_case_test_object() {
        type T = TestObject;
        let layout = Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
            .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }

    #[test]
    fn header_align_general_size_returns_new_cache_case_u8() {
        type T = u8;
        let layout = Layout::from_size_align(safe_slab_size::<T>(5), align_of::<SlabHeader<T>>())
            .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }

    #[test]
    fn multiple_header_align_general_size_returns_new_cache_case_test_object() {
        type T = TestObject;
        let layout =
            Layout::from_size_align(safe_slab_size::<T>(5), 2 * align_of::<SlabHeader<T>>())
                .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }

    #[test]
    fn multiple_header_align_general_size_returns_new_cache_case_u64() {
        type T = u64;
        let layout =
            Layout::from_size_align(safe_slab_size::<T>(5), 4 * align_of::<SlabHeader<T>>())
                .expect("Failed to create the layout");

        let mut cache = Cache::<T>::new(['c'; CACHE_NAME_LENGTH], layout);

        unsafe { verify_cache_invariants(&raw mut cache) };
        assert_eq!(
            0,
            unsafe { cache_slabs(&raw mut cache).len() },
            "The new cache should contain no slabs"
        );
    }
}

#[cfg(test)]
mod cache_allocate_object_test {
    extern crate alloc;

    use crate::mem::slab::Error::NoSlabAvailable;
    use crate::mem::slab::test_utils::{
        SlabMan, TestObject, TestObject2, prepend_new_slabs, safe_slab_layout,
        verify_cache_invariants_v2,
    };
    use crate::mem::slab::{CACHE_NAME_LENGTH, Cache, SlabHeader};
    use alloc::vec;
    use alloc::vec::Vec;
    use core::fmt::Debug;
    use core::ptr::null_mut;

    type Type1 = TestObject;
    type Type2 = TestObject2;
    type Type3 = u8;

    fn test_null_cache_panics<T: Default>() {
        let _ = unsafe { Cache::<T>::allocate_object(null_mut()) };
    }

    test_panic_against_types!(
        test_null_cache_panics,
        "Cache::allocate_object: cache should not be null",
        (null_cache_panics_for_type1, Type1),
        (null_cache_panics_for_type2, Type2),
        (null_cache_panics_for_type3, Type3),
    );

    fn test_no_slabs_returns_no_slab_available_err_cache_unmodified<T: Default + Debug>() {
        // Arrange:
        // Create a cache with no slabs.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let slab_man = SlabMan::<T>::new(layout);
        let allocated_objects = Vec::new();

        assert_eq!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should be null initially"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };

        // Assert
        assert!(
            result.is_err(),
            "The result should be Err(NoSlabAvailable) but got {result:?}"
        );

        let err = result.unwrap_err();
        assert!(
            matches!(err, NoSlabAvailable),
            "The error should be {:?} but got {err:?}",
            NoSlabAvailable,
        );

        assert_eq!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should remain null after the allocation"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should remain null after the allocation"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should remain null after the allocation"
        );

        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &allocated_objects,
            );
        }
    }

    test_against_types!(
        test_no_slabs_returns_no_slab_available_err_cache_unmodified,
        (
            no_slabs_returns_no_slab_available_err_cache_unmodified_for_type1,
            Type1
        ),
        (
            no_slabs_returns_no_slab_available_err_cache_unmodified_for_type2,
            Type2
        ),
        (
            no_slabs_returns_no_slab_available_err_cache_unmodified_for_type3,
            Type3
        ),
    );

    fn test_full_slabs_only_returns_no_slab_available_err_cache_unmodified<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains only two full slabs.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                2,
                &Vec::new(),
                0,
            );
        }

        assert_ne!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should not be null initially"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };

        // Assert
        assert!(
            result.is_err(),
            "The result should be Err(NoSlabAvailable) but got {result:?}"
        );

        let err = result.unwrap_err();
        assert!(
            matches!(err, NoSlabAvailable),
            "The error should be {:?} but got {err:?}",
            NoSlabAvailable,
        );

        assert_ne!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should remain not null after the allocation"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should remain null after the allocation"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should remain null after the allocation"
        );

        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_full_slabs_only_returns_no_slab_available_err_cache_unmodified,
        (
            full_slabs_only_returns_no_slab_available_err_cache_unmodified_for_type1,
            Type1
        ),
        (
            full_slabs_only_returns_no_slab_available_err_cache_unmodified_for_type2,
            Type2
        ),
        (
            full_slabs_only_returns_no_slab_available_err_cache_unmodified_for_type3,
            Type3
        ),
    );

    fn test_returned_object_has_default_value_for_empty<T: Default + Debug + PartialEq>() {
        // Arrange:
        // Create a cache that contains a single empty slab.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                0,
                &Vec::new(),
                1,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially to ensure the object is allocated from the empty slab"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            &T::default(),
            allocated_object.get_ref(),
            "The allocated object should have the default value"
        );
    }

    test_against_types!(
        test_returned_object_has_default_value_for_empty,
        (returned_object_has_default_value_for_empty_type1, Type1),
        (returned_object_has_default_value_for_empty_type2, Type2),
        (returned_object_has_default_value_for_empty_type3, Type3),
    );

    fn test_returned_object_has_default_value_for_partial<T: Default + Debug + PartialEq>() {
        // Arrange:
        // Create a cache that contains a single partial slab.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(4);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                1,
                &vec![2],
                0,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially to ensure the object is allocated from the partial slab"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            &T::default(),
            allocated_object.get_ref(),
            "The allocated object should have the default value"
        );
    }

    test_against_types!(
        test_returned_object_has_default_value_for_partial,
        (returned_object_has_default_value_for_partial_type1, Type1),
        (returned_object_has_default_value_for_partial_type2, Type2),
        (returned_object_has_default_value_for_partial_type3, Type3),
    );

    fn test_returned_object_has_correct_source_for_empty<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains one empty slab and two full slabs.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                2,
                &Vec::new(),
                1,
            );
        }
        let empty_slab = cache.slabs_empty;

        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially to ensure the object is allocated from the empty slab"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            empty_slab, allocated_object.source,
            "The allocated object should come from the empty slab"
        );
    }

    test_against_types!(
        test_returned_object_has_correct_source_for_empty,
        (returned_object_has_correct_source_for_empty_type1, Type1),
        (returned_object_has_correct_source_for_empty_type2, Type2),
        (returned_object_has_correct_source_for_empty_type3, Type3),
    );

    fn test_returned_object_has_correct_source_for_partial<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains one partial slab and two full slabs.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(4);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                2,
                &vec![2],
                0,
            );
        }
        let partial_slab = cache.slabs_partial;

        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially to ensure the object is allocated from the partial slab"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            partial_slab, allocated_object.source,
            "The allocated object should come from the partial slab"
        );
    }

    test_against_types!(
        test_returned_object_has_correct_source_for_partial,
        (returned_object_has_correct_sorce_for_partial_type1, Type1),
        (returned_object_has_correct_sorce_for_partial_type2, Type2),
        (returned_object_has_correct_sorce_for_partial_type3, Type3),
    );

    fn test_slabs_empty_becomes_null<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains a single empty slab.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                0,
                &Vec::new(),
                1,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially to ensure the object is allocated from the empty slab"
        );
        assert_ne!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should not be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null after the allocation"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_slabs_empty_becomes_null,
        (slabs_empty_becomes_null_for_type1, Type1),
        (slabs_empty_becomes_null_for_type2, Type2),
        (slabs_empty_becomes_null_for_type3, Type3),
    );

    fn test_slabs_partial_becomes_non_null<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains two empty slabs.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                0,
                &Vec::new(),
                2,
            );
        }
        let empty_slab1 = cache.slabs_empty;

        assert!(
            unsafe { (*empty_slab1).total_slots > 1 },
            "The empty slabs should have more than one free slot to ensure a partial slab after the allocation"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_ne!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should not be null after the allocation"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_slabs_partial_becomes_non_null,
        (slabs_partial_becomes_non_null_for_type1, Type1),
        (slabs_partial_becomes_non_null_for_type2, Type2),
        (slabs_partial_becomes_non_null_for_type3, Type3),
    );

    fn test_slabs_partial_becomes_null<T: Default + Debug>() {
        // Arrange:
        // create a cache that contains a partial slab that is one free slot left and
        // a full slab.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                1,
                &vec![1],
                0,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially to ensure the object is allocated from the partial slab"
        );
        assert_ne!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should not be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null after the allocation"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_slabs_partial_becomes_null,
        (slabs_partial_becomes_null_for_type1, Type1),
        (slabs_partial_becomes_null_for_type2, Type2),
        (slabs_partial_becomes_null_for_type3, Type3),
    );

    fn test_slabs_full_becomes_non_null<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains a partial slab that is one free slot left.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                0,
                &vec![1],
                0,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should be null initially"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        assert_ne!(
            null_mut(),
            cache.slabs_full,
            "The slabs_full should not be null after the allocation"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_slabs_full_becomes_non_null,
        (slabs_full_becomes_non_null_for_type1, Type1),
        (slabs_full_becomes_non_null_for_type2, Type2),
        (slabs_full_becomes_non_null_for_type3, Type3),
    );

    fn test_empty_slab_becomes_partial<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains two empty slabs and a full slab.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                1,
                &Vec::new(),
                2,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially to ensure the object is allocated from the empty slabs"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        let moved_slab = allocated_object.source;
        assert!(
            unsafe { !SlabHeader::is_full(moved_slab) },
            "The moved slab should not be full"
        );
        assert!(
            unsafe { !SlabHeader::is_empty(moved_slab) },
            "The moved slab should not be empty"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_empty_slab_becomes_partial,
        (empty_slab_becomes_partial_for_type1, Type1),
        (empty_slab_becomes_partial_for_type2, Type2),
        (empty_slab_becomes_partial_for_type3, Type3),
    );

    fn test_empty_slab_becomes_full<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains two empty slabs and a full slab. All slabs have a
        // total_slots of one.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(1);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                1,
                &Vec::new(),
                2,
            );
        }
        let empty_slab1 = cache.slabs_empty;

        assert_eq!(
            1,
            unsafe { (*empty_slab1).total_slots },
            "The slabs should have a total slots of one"
        );
        assert_eq!(
            null_mut(),
            cache.slabs_partial,
            "The slabs_partial should be null initially to ensure the object is allocated from the empty slabs"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        let moved_slab = allocated_object.source;
        assert!(
            unsafe { SlabHeader::is_full(moved_slab) },
            "The moved slab should be full"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_empty_slab_becomes_full,
        (empty_slab_becomes_full_for_type1, Type1),
        (empty_slab_becomes_full_for_type2, Type2),
    );

    fn test_partial_slab_remains_partial<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains two partial slabs. Both partial slabs have more than one
        // available slot.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(4);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                0,
                &vec![3, 2],
                0,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially to ensure the object is allocated from the partial slabs"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        let moved_slab = allocated_object.source;
        assert!(
            unsafe { !SlabHeader::is_full(moved_slab) },
            "The moved slab should not be full"
        );
        assert!(
            unsafe { !SlabHeader::is_empty(moved_slab) },
            "The moved slab should not be empty"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_partial_slab_remains_partial,
        (partial_slab_remains_partial_for_type1, Type1),
        (partial_slab_remains_partial_for_type2, Type2),
        (partial_slab_remains_partial_for_type3, Type3),
    );

    fn test_partial_slab_becomes_full<T: Default + Debug>() {
        // Arrange:
        // Create a cache that contains two partial slabs and one full slab. Both partial slabs
        // have only one slot available.
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(2);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                1,
                &vec![1, 1],
                0,
            );
        }

        assert_eq!(
            null_mut(),
            cache.slabs_empty,
            "The slabs_empty should be null initially to ensure the object is allocated from a partial slab"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        let moved_slab = allocated_object.source;
        assert!(
            unsafe { SlabHeader::is_full(moved_slab) },
            "The moved slab should be full"
        );

        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types!(
        test_partial_slab_becomes_full,
        (partial_slab_becomes_full_for_type1, Type1),
        (partial_slab_becomes_full_for_type2, Type2),
        (partial_slab_becomes_full_for_type3, Type3),
    );

    fn test_general_case<T: Default + Debug>(
        total_slots: usize,
        new_fulls: usize,
        new_partial_free_slots: &[usize],
        new_empties: usize,
    ) {
        // Arrange
        let name = ['c'; CACHE_NAME_LENGTH];
        let layout = safe_slab_layout::<T>(total_slots);

        let mut cache = Cache::<T>::new(name, layout);
        let mut slab_man = SlabMan::<T>::new(layout);
        let mut slab_objects = Vec::new();

        unsafe {
            prepend_new_slabs(
                &raw mut cache,
                &mut slab_man,
                &mut slab_objects,
                new_fulls,
                new_partial_free_slots,
                new_empties,
            );
        }

        let slab = if new_fulls > 0 {
            cache.slabs_full
        } else if new_partial_free_slots.len() > 0 {
            cache.slabs_partial
        } else {
            assert!(
                new_empties > 0,
                "The cache should contain at least one slab"
            );
            cache.slabs_empty
        };

        assert_eq!(
            total_slots,
            unsafe { (*slab).total_slots },
            "There is discrepancy between the desired total_slots and the actual total_slots"
        );

        // Act
        let result = unsafe { Cache::allocate_object(&raw mut cache) };
        assert!(result.is_ok(), "The result should be Ok but got {result:?}");
        let allocated_object = result.unwrap();

        // Assert
        slab_objects.push(allocated_object);
        unsafe {
            verify_cache_invariants_v2(
                &raw mut cache,
                &name,
                layout,
                slab_man.allocated_addrs(),
                &slab_objects,
            );
        }
    }

    test_against_types_arguments!(
        test_general_case,
        (general_case_1, Type1, 2, 4, &vec![], 2),
        (general_case_2, Type1, 4, 1, &vec![2, 3], 0),
        (general_case_3, Type2, 3, 2, &vec![1, 2], 3),
        (general_case_4, Type2, 4, 0, &vec![3, 2], 1),
    );
}

#[cfg(test)]
mod cache_pop_front_test {
    extern crate alloc;

    use crate::mem::slab::Cache;
    use crate::mem::slab::test_utils::{
        SlabMan, collect_list_slabs, contains_node, create_slab_list, safe_slab_layout,
        size_of_list, verify_list_doubly_linked, verify_node_isolated,
    };
    use alloc::vec;
    use core::ptr::null_mut;

    type T = u8;

    #[test]
    #[should_panic(expected = "Cache::pop_front: head should not be null")]
    fn null_head_panics() {
        let _ = unsafe { Cache::<T>::pop_front(null_mut()) };
    }

    #[test]
    #[should_panic(expected = "Cache::pop_front: head should not have its prev linked")]
    fn head_has_prev_linked_panics() {
        // Arrange:
        // Create a head with its prev linked.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let prev = create_slab_list(&mut slab_man, 2);
        let head = unsafe { (*prev).next };

        // Act
        unsafe { Cache::pop_front(head) };
    }

    #[test]
    fn single_node_list_returns_head_and_null() {
        // Arrange:
        // Create a head containing a single node.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::new(layout);
        let head = slab_man.new_test_slab(null_mut());

        // Act
        let (node, new_head) = unsafe { Cache::<T>::pop_front(head) };

        // Assert
        unsafe { verify_node_isolated(node) };

        assert_eq!(node, head, "The detached node should be the original head");
        assert_eq!(null_mut(), new_head, "The new head should be null");
    }

    #[test]
    fn two_nodes_list_returns_head_and_next() {
        // Arrange:
        // Create a head containing two nodes.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let head = create_slab_list(&mut slab_man, 2);
        let next = unsafe { (*head).next };

        // Act
        let (node, new_head) = unsafe { Cache::pop_front(head) };

        // Assert
        unsafe { verify_node_isolated(node) };
        unsafe { verify_list_doubly_linked(new_head) };

        assert_eq!(node, head, "The detached node should be the original head");
        assert_eq!(
            next, new_head,
            "The new head should be the next of the original head"
        );
        assert_eq!(
            1,
            unsafe { size_of_list(new_head) },
            "The new head should contain one node"
        );
    }

    #[test]
    fn multi_nodes_list_returns_head_and_next() {
        // Arrange:
        // Create a head containing three nodes.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let head = create_slab_list(&mut slab_man, 3);
        let next = unsafe { (*head).next };
        let next_next = unsafe { (*next).next };

        // Act
        let (node, new_head) = unsafe { Cache::pop_front(head) };

        // Assert
        unsafe { verify_node_isolated(node) };
        unsafe { verify_list_doubly_linked(new_head) };

        assert_eq!(node, head, "The detached node should be the original head");
        assert_eq!(
            next, new_head,
            "The new head should be the next of the original head"
        );
        assert_eq!(
            2,
            unsafe { size_of_list(new_head) },
            "The new head should contain two nodes"
        );
        assert!(
            unsafe { contains_node(new_head, next_next) },
            "The new head should contain the next_next"
        );
    }

    #[test]
    fn multi_nodes_list_new_head_preserve_node_order() {
        // Arrange:
        // Create a head containing four nodes.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let head = create_slab_list(&mut slab_man, 4);
        let next = unsafe { (*head).next };
        let next_next = unsafe { (*next).next };
        let next_next_next = unsafe { (*next_next).next };

        // Act
        let (node, new_head) = unsafe { Cache::pop_front(head) };

        // Assert
        unsafe { verify_node_isolated(node) };
        unsafe { verify_list_doubly_linked(new_head) };

        assert_eq!(
            vec![next, next_next, next_next_next],
            unsafe { collect_list_slabs(new_head) },
            "The new head should contain the expected nodes in the correct order"
        );
    }
}

#[cfg(test)]
mod cache_push_front_test {
    extern crate alloc;

    use crate::mem::slab::Cache;
    use crate::mem::slab::test_utils::{
        SlabMan, collect_list_slabs, create_slab_list, safe_slab_layout, size_of_list,
        verify_list_doubly_linked,
    };
    use alloc::vec;
    use core::ptr::null_mut;

    type T = u8;

    #[test]
    #[should_panic(expected = "Cache::push_front: node should not be null")]
    fn null_head_null_node_panics() {
        let _ = unsafe { Cache::<T>::push_front(null_mut(), null_mut()) };
    }

    #[test]
    #[should_panic(expected = "Cache::push_front: node should not be null")]
    fn valid_head_null_node_panics() {
        // Arrange:
        // Create a head containing two nodes
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::new(layout);
        let head = create_slab_list(&mut slab_man, 2);

        // Act
        let _ = unsafe { Cache::<T>::push_front(head, null_mut()) };
    }

    #[test]
    #[should_panic(expected = "Cache::push_front: head should not have its prev linked")]
    fn head_has_prev_linked_panics() {
        // Arrange:
        // Create a head with its prev linked and a node to be pushed.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let prev = create_slab_list(&mut slab_man, 2);
        let head = unsafe { (*prev).next };
        let node = slab_man.new_test_slab(null_mut());

        // Act
        unsafe { Cache::push_front(head, node) };
    }

    #[test]
    #[should_panic(expected = "Cache::push_front: node should not have its prev linked")]
    fn node_has_prev_linked_panics() {
        // Arrange:
        // Create a node with its prev linked.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let prev = create_slab_list(&mut slab_man, 2);
        let node = unsafe { (*prev).next };

        // Act
        unsafe { Cache::push_front(null_mut(), node) };
    }

    #[test]
    #[should_panic(expected = "Cache::push_front: node should not have its next linked")]
    fn node_has_next_linked_panics() {
        // Arrange:
        // Create a node with its next linked.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let node = create_slab_list(&mut slab_man, 2);

        // Act
        unsafe { Cache::push_front(null_mut(), node) };
    }

    #[test]
    fn null_head_valid_node_returns_node() {
        // Arrange:
        // Create the node to be inserted.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let node = slab_man.new_test_slab(null_mut());

        // Act
        let new_head = unsafe { Cache::push_front(null_mut(), node) };

        // Assert
        assert_eq!(node, new_head, "The new head should be the node");
        assert_eq!(
            1,
            unsafe { size_of_list(new_head) },
            "The new head should contain one node"
        );

        unsafe { verify_list_doubly_linked(new_head) };
    }

    #[test]
    fn valid_head_valid_node_returns_node_preserve_order() {
        // Arrange:
        // Create a head containing two nodes and a node to be inserted.
        let layout = safe_slab_layout::<T>(2);
        let mut slab_man = SlabMan::<T>::new(layout);
        let head = create_slab_list(&mut slab_man, 2);
        let next = unsafe { (*head).next };
        let node = slab_man.new_test_slab(null_mut());

        // Act
        let new_head = unsafe { Cache::push_front(head, node) };

        // Assert
        assert_eq!(node, new_head, "The new head should be the node");
        assert_eq!(
            vec![new_head, head, next],
            unsafe { collect_list_slabs(node) },
            "The new head should contain the expected nodes in the correct order"
        );

        unsafe { verify_list_doubly_linked(new_head) };
    }
}

#[cfg(test)]
mod cache_tests {
    extern crate alloc;
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
}

#[cfg(test)]
mod header_tests {
    extern crate alloc;

    use super::*;
    use crate::mem::slab::test_utils::{
        SlabMan, TestObject, safe_slab_size, slab_allocated_addrs, verify_slab_invariants,
    };
    use Error::NotAnObjectOfCurrentSlab;
    use alloc::vec::Vec;
    use alloc::{format, vec};
    use core::any::type_name;

    #[test]
    #[should_panic(expected = "SlabHeader::compute_slot0_offset: result overflow")]
    fn compute_slot0_offset_result_overflow_panics() {
        let _ = SlabHeader::<u64>::compute_slot0_offset(0, usize::MAX - 2);
    }

    #[test]
    fn compute_slot0_offset_header_end_overflow_returns_expected_offset() {
        // aligned header end
        assert_compute_slot0_offset::<u32>(9, usize::MAX, 9);
        assert_compute_slot0_offset::<u32>(9, usize::MAX - 8, 9);

        // unaligned header end
        assert_compute_slot0_offset::<u32>(9, usize::MAX, 8);
        assert_compute_slot0_offset::<u32>(9, usize::MAX - 8, 8);
    }

    #[test]
    fn compute_slot0_offset_aligned_header_end_return_header_size() {
        assert_compute_slot0_offset::<u8>(5, 5, 5);
        assert_compute_slot0_offset::<u8>(8, 8, 8);

        assert_compute_slot0_offset::<u32>(4, 4, 4);
        assert_compute_slot0_offset::<u32>(32, 32, 32);
        assert_compute_slot0_offset::<u32>(6, 38, 6);
        assert_compute_slot0_offset::<u32>(18, 82, 18);

        assert_compute_slot0_offset::<u64>(8, 16, 8);
        assert_compute_slot0_offset::<u64>(16, 16, 16);
        assert_compute_slot0_offset::<u64>(4, 12, 4);
        assert_compute_slot0_offset::<u64>(10, 30, 10);
    }

    #[test]
    fn compute_slot0_offset_unaligned_header_end_returns_correct_offset() {
        assert_compute_slot0_offset::<u32>(20, 16, 18);
        assert_compute_slot0_offset::<u32>(21, 15, 19);

        assert_compute_slot0_offset::<u64>(40, 40, 35);
        assert_compute_slot0_offset::<u64>(42, 38, 37);
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
    use core::cmp::max;
    use core::ptr::{NonNull, null_mut};

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

    #[derive(Debug, PartialEq)]
    pub struct TestObject2 {
        x: TestObject,
        y: TestObject,
        z: u128,
    }

    impl Default for TestObject2 {
        fn default() -> Self {
            Self {
                x: TestObject::default(),
                y: TestObject {
                    x: 121,
                    y: 222,
                    z: 306,
                },
                z: 9124,
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

        pub fn allocated_addrs(&self) -> &Vec<*mut u8> {
            &(self.allocated)
        }
    }

    impl<T: Default> Drop for SlabMan<T> {
        fn drop(&mut self) {
            unsafe { release_memory(&self.allocated, self.slab_layout) }
        }
    }

    /// `prepend_new_slabs` prepends `new_empties` empty slabs to the `slabs_empty`, `new_fulls`
    /// full slabs to the `slabs_full`, and partial slabs according to `new_partial_free_slots`
    /// to the `slabs_partial`. All slabs are acquired from the `slab_man`, and all allocated
    /// objects are appended to the `slab_objects`.
    ///
    ///
    /// # Safety
    /// * `cache` must be a valid pointer and in a valid state.
    /// * `cache` and `slab_man` must have a compatible slab layout.
    ///
    /// # Panics
    /// This function will panic if any target-free slots in the `new_partial_free_slots` result
    /// in either an empty slab or a full slab.
    pub unsafe fn prepend_new_slabs<T: Default>(
        cache: *mut Cache<T>,
        slab_man: &mut SlabMan<T>,
        slab_object: &mut Vec<SlabObject<T>>,
        new_fulls: usize,
        new_partial_free_slots: &[usize],
        new_empties: usize,
    ) {
        for &target_free_slots in new_partial_free_slots.iter() {
            prepend_new_partial_slab(cache, slab_man, slab_object, target_free_slots);
        }
        for _ in 0..new_empties {
            prepend_new_empty_slab(cache, slab_man);
        }
        for _ in 0..new_fulls {
            prepend_new_full_slab(cache, slab_man, slab_object)
        }
    }

    /// `prepend_new_empty_slab` prepends an empty slab to the `slabs_empty` of the `cache`.
    /// This empty slab is acquired from the `slab_man`.
    ///
    /// # Safety
    /// * `cache` must be a valid pointer and in a valid state.
    /// * `cache` and `slab_man` must have a compatible slab layout.
    unsafe fn prepend_new_empty_slab<T: Default>(cache: *mut Cache<T>, slab_man: &mut SlabMan<T>) {
        let new_slab = slab_man.new_test_slab(cache);

        if !(*cache).slabs_empty.is_null() {
            (*new_slab).next = (*cache).slabs_empty;
            (*(*cache).slabs_empty).prev = new_slab;
        }
        (*cache).slabs_empty = new_slab;
    }

    /// `prepend_new_partial_slab` prepends a partial slab to the `slabs_partial` of the
    /// `cache`. This partial slab is acquired from the `slab_man`. It contains
    /// `target_free_slots`, and all its allocated objects are appended to the `slab_objects`.
    ///
    /// # Safety
    /// * `cache` must be a valid pointer and in a valid state.
    /// * `cache` and `slab_man` must have a compatible slab layout.
    ///
    /// # Panics
    /// This function will panic if the `target_free_slots` results in either an empty slab
    /// or a full slab.
    unsafe fn prepend_new_partial_slab<T: Default>(
        cache: *mut Cache<T>,
        slab_man: &mut SlabMan<T>,
        slab_objects: &mut Vec<SlabObject<T>>,
        target_free_slots: usize,
    ) {
        assert!(
            target_free_slots > 0,
            "A partial slab should have at least one free slot"
        );

        let new_slab = slab_man.new_test_slab(cache);
        assert!(
            target_free_slots < (*new_slab).total_slots,
            "A partial slab should have at least one slot used"
        );

        let used_slots = (*new_slab).total_slots - target_free_slots;
        for _ in 0..used_slots {
            slab_objects
                .push(SlabHeader::allocate_object(new_slab).expect("Failed to allocate object"));
        }

        if !(*cache).slabs_partial.is_null() {
            (*new_slab).next = (*cache).slabs_partial;
            (*(*cache).slabs_partial).prev = new_slab;
        }
        (*cache).slabs_partial = new_slab;
    }

    /// `prepend_new_full_slab` prepends a full slab to the `slabs_full` of the `cache`.
    /// This full slab is acquired from the `slab_man`, and all its allocated objects are
    /// appended to the `slab_objects`.
    ///
    /// # Safety
    /// * `cache` must be a valid pointer and in a valid state.
    /// * `cache` and `slab_man` must have a compatible slab layout.
    unsafe fn prepend_new_full_slab<T: Default>(
        cache: *mut Cache<T>,
        slab_man: &mut SlabMan<T>,
        slab_objects: &mut Vec<SlabObject<T>>,
    ) {
        let new_slab = slab_man.new_test_slab(cache);
        while !SlabHeader::is_full(new_slab) {
            slab_objects
                .push(SlabHeader::allocate_object(new_slab).expect("Failed to allocate object"));
        }

        if !(*cache).slabs_full.is_null() {
            (*new_slab).next = (*cache).slabs_full;
            (*(*cache).slabs_full).prev = new_slab;
        }
        (*cache).slabs_full = new_slab;
    }

    /// `safe_slab_layout` returns a layout that complies with the slab alignment and
    /// can accommodate `total_slots`. It assumes the slot size is equal to the size of `T`.
    ///
    /// Please be aware that the size returned may lead to an actual `total_slots`
    /// larger than the given value.
    ///
    /// # Panics
    /// This function will panic when
    /// * The `total_slots` is zero.
    /// * The resulting size overflows isize.
    pub fn safe_slab_layout<T: Default>(total_slots: usize) -> Layout {
        assert!(
            total_slots > 0,
            "The total_slots should be greater than zero"
        );

        let size = safe_slab_size::<T>(total_slots);
        let align = Cache::<T>::align_of_slab();
        Layout::from_size_align(size, align).expect("Failed to create layout")
    }

    /// `safe_slab_size` returns a slab size that can accommodate `total_slots`.
    /// It assumes the slot size is equal to the size of `T`.
    ///
    /// Please be aware that the size returned may lead to an actual `total_slots`
    /// larger than the given value.
    ///
    /// # Panics
    /// This function will panic if `total_slots` is zero.
    pub fn safe_slab_size<T: Default>(total_slots: usize) -> ByteSize {
        assert!(
            total_slots > 0,
            "The total_slots should be greater than zero"
        );

        max(
            Cache::<T>::min_slab_size(),
            size_of::<SlabHeader<T>>() + align_of::<T>() + size_of::<T>() * total_slots,
        )
    }

    /// Verify if the `cache` satisfies the invariants of a [Cache].
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    pub unsafe fn verify_cache_invariants<T: Default>(cache: *mut Cache<T>) {
        verify_cache_type(cache);
        verify_cache_slab_layout(cache, (*cache).slab_layout);
        verify_cache_slabs_full(cache);
        verify_cache_slabs_partial(cache);
        verify_cache_slabs_empty(cache);
    }

    /// Verify if the `cache` satisfies the invariants of a [Cache].
    // todo!(list the checked invariants)
    // todo!(rename to verify_cache_invariants after the old function is removed)
    ///
    /// # SAFETY:
    /// * `cache` must be a valid pointer.
    pub unsafe fn verify_cache_invariants_v2<T: Default>(
        cache: *mut Cache<T>,
        expected_name: &[char; CACHE_NAME_LENGTH],
        expected_layout: Layout,
        expected_slabs: &Vec<*mut u8>,
        expected_objects: &Vec<SlabObject<T>>,
    ) {
        verify_cache_name(
            cache,
            expected_name,
            "The cache name doesn't match the expected",
        );

        verify_cache_type(cache);
        verify_cache_slab_layout(cache, expected_layout);
        verify_cache_slabs_full(cache);
        verify_cache_slabs_partial(cache);
        verify_cache_slabs_empty(cache);

        verify_contained_slabs(
            cache,
            expected_slabs,
            "The contained slabs don't match the expected",
        );
        verify_allocated_objects(
            cache,
            expected_objects,
            "The allocated objects don't match the expected",
        );
    }

    /// Verify if the `cache` has the expected `name`.
    ///
    /// # Safety:
    /// * `cache` must be a valid pointer.
    pub unsafe fn verify_cache_name<T: Default>(
        cache: *mut Cache<T>,
        name: &[char; CACHE_NAME_LENGTH],
        err_message: &str,
    ) {
        assert_eq!(name, &(*cache).name, "{}", err_message);
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
    unsafe fn verify_cache_slab_layout<T: Default>(cache: *mut Cache<T>, expected_layout: Layout) {
        assert_eq!(
            expected_layout,
            (*cache).slab_layout,
            "The slab layout doesn't match the expected"
        );
        assert!(
            Cache::<T>::min_slab_size() <= (*cache).slab_layout.size(),
            "The size of the slab layout does not meet the min slab size requirement"
        );
        assert_eq!(
            0,
            (*cache).slab_layout.align() % align_of::<SlabHeader<T>>(),
            "The alignment of the slab layout is incompatible with SlabHeader<T>"
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
            assert!(
                SlabHeader::is_empty(curr),
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

    pub unsafe fn verify_contained_slabs<T: Default>(
        cache: *mut Cache<T>,
        expected_slabs: &Vec<*mut u8>,
        err_message: &str,
    ) {
        let mut expected_addrs = expected_slabs
            .iter()
            .map(|&slab| slab.addr())
            .collect::<Vec<_>>();
        expected_addrs.sort();

        let mut actual_addrs = cache_slabs::<T>(cache)
            .iter()
            .map(|header| header.addr())
            .collect::<Vec<_>>();
        actual_addrs.sort();

        assert_eq!(expected_addrs, actual_addrs, "{}", err_message,);
    }

    pub unsafe fn verify_allocated_objects<T: Default>(
        cache: *mut Cache<T>,
        expected_objects: &Vec<SlabObject<T>>,
        err_message: &str,
    ) {
        let mut expected_addrs = expected_objects
            .iter()
            .map(|slab_object| slab_object.object.addr())
            .collect::<Vec<_>>();
        expected_addrs.sort();

        let mut actual_addrs = cache_allocated_addrs(cache);
        actual_addrs.sort();

        assert_eq!(expected_addrs, actual_addrs, "{}", err_message,);
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
        result.append(&mut collect_list_slabs((*cache).slabs_full));
        result.append(&mut collect_list_slabs((*cache).slabs_partial));
        result.append(&mut collect_list_slabs((*cache).slabs_empty));
        result
    }

    /// `collect_list_slabs` returns a list containing the `head` and the slabs after it.
    /// The slabs on the `prev` side of the `head` are ignored.
    ///
    /// The order of the slabs is preserved.
    ///
    /// # SAFETY:
    /// * `head` must be either null or a pointer to a valid doubly-linked slab list.
    pub unsafe fn collect_list_slabs<T: Default>(
        head: *mut SlabHeader<T>,
    ) -> Vec<*mut SlabHeader<T>> {
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

    /// `create_slab_list` creates a doubly-linked list of [SlabHeader] and returns its head.
    ///
    /// Each slab is empty, has a null `source` and has a layout determined by the `slab_man`.
    pub fn create_slab_list<T: Default>(
        slab_man: &mut SlabMan<T>,
        size: usize,
    ) -> *mut SlabHeader<T> {
        assert_ne!(
            0, size,
            "test_utils::create_slab_list: size should not be zero"
        );

        let mut vec = Vec::new();
        for _ in 0..size {
            vec.push(slab_man.new_test_slab(null_mut()));
        }

        for i in 1..size {
            unsafe {
                (*vec[i - 1]).next = vec[i];
                (*vec[i]).prev = vec[i - 1];
            }
        }
        vec[0]
    }

    #[test]
    #[should_panic(expected = "test_utils::create_slab_list: size should not be zero")]
    fn create_slab_list_zero_size_panics() {
        // Create a SlabMan
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        // Exercise create_slab_list with zero size
        let _ = create_slab_list(&mut slab_man, 0);
    }

    #[test]
    fn create_slab_list_valid_arguments_returns_head_correct_size() {
        // Create a SlabMan
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        // Exercise create_slab_list
        let head = create_slab_list(&mut slab_man, 3);

        // Verify the size of the returned head
        assert_eq!(
            3,
            unsafe { collect_list_slabs(head).len() },
            "The size of head is incorrect"
        );
    }

    #[test]
    fn create_slab_list_valid_arguments_returns_head_doubly_linked() {
        // Create a SlabMan
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        // Exercise create_slab_list
        let head = create_slab_list(&mut slab_man, 2);

        // Verify whether the returned head is doubly linked
        unsafe { verify_list_doubly_linked(head) };
    }

    #[test]
    fn create_slab_list_valid_arguments_returns_null_source_slabs() {
        // Create a SlabMan
        type T = u8;
        let slab_layout =
            Layout::from_size_align(safe_slab_size::<T>(2), align_of::<SlabHeader<T>>())
                .expect("Failed to create slab_layout");
        let mut slab_man = SlabMan::<T>::new(slab_layout);

        // Exercise create_slab_list
        let head = create_slab_list(&mut slab_man, 3);

        // Verify whether each slab has a null source
        for slab in unsafe { collect_list_slabs(head) } {
            assert_eq!(
                null_mut(),
                unsafe { (*slab).source },
                "The source of each slab should be null"
            );
        }
    }
}
