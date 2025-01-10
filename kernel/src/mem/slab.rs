// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::dsa::ListNode;
use crate::lock::Spinlock;
use crate::HasHole;
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

impl HasHole for Slab {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}
