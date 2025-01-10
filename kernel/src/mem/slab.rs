// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::dsa::ListNode;
use crate::lock::Spinlock;
use crate::HasHole;
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

impl HasHole for Cache {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}

#[repr(C)]
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
    fn initialize<T>(&mut self, cache: &mut Cache)
    where
        T: Default + HasHole,
    {
        // Offset from the first slot's address to this slab's address.
        let slot0_offset = Bytes(size_of::<Self>());
        let slot_size = Bytes(size_of::<T>());

        self.unlink_hole();
        self.reset_used_bitmap_and_count();
        self.set_slot0_and_total_slots(slot0_offset, cache.slab_size, slot_size);
        self.install_objects::<T>(cache.hole(), slot_size);
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

    fn set_slot0_and_total_slots(
        &mut self,
        slot0_offset: Bytes,
        slab_size: Bytes,
        slot_size: Bytes,
    ) {
        let base_addr = Address::from(self as *mut Slab);
        self.slot0 = base_addr + slot0_offset;

        let slot_space = Bytes(slab_size.0 - slot0_offset.0);
        self.total_slots = (slot_space.0 / slot_size.0).max(MAX_SLOTS_PER_SLAB);
    }

    /// For each slot, install the default value of struct [T];
    /// Then, link its hole.[prev] to the [Cache] and its hole.[next] to this [Slab].
    fn install_objects<T>(&mut self, cache_hole: &mut ListNode, slot_size: Bytes)
    where
        T: Default + HasHole,
    {
        let mut start = self.slot0;
        for _ in 0..self.total_slots {
            let mut object = T::default();
            object.hole().prev.store(cache_hole, Relaxed);
            object.hole().next.store(self.hole(), Relaxed);

            unsafe {
                (start.0 as *mut T).write(object);
            }
            start = start + slot_size;
        }
    }
}

impl HasHole for Slab {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}
