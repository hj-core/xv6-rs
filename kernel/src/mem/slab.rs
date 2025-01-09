// Ref:
// Understanding the Linux Virtual Memory Manager by Mel Gorman, Chapter 8
// https://pdos.csail.mit.edu/~sbw/links/gorman_book.pdf

use crate::dsa::ListNode;
use crate::HasHole;
use wrapper::{Address, Bytes};

const CACHE_NAME_LENGTH: usize = 8;
const SLAB_USED_BITMAP_SIZE: usize = 4;
const MAX_OBJECTS_PER_SLAB: usize = SLAB_USED_BITMAP_SIZE * 64;

#[repr(C)]
struct Cache {
    /// The hole and other holes in the [Cache] chain are circularly linked.
    hole: ListNode,
    slabs_full: ListNode,
    slabs_partial: ListNode,
    slabs_empty: ListNode,
    slab_size: Bytes,
    name: [char; CACHE_NAME_LENGTH],
}

impl HasHole for Cache {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}

#[repr(C)]
struct Slab {
    /// The hole's [prev] is linked to the [hole] of the [Cache] owning this [Slab],
    /// and the hole's [next] is linked to the hole of the next [Slab] in the [Slab] list.
    hole: ListNode,
    /// Each bit indicates whether an object is used;
    /// bit 0 of the first u64 is object 0, bit 1 is object 1,
    /// bit 0 of the second u64 is object 64, bit 1 is object 65, and so on.
    used_bitmap: [u64; SLAB_USED_BITMAP_SIZE],
    used_count: usize,
    object0: Address,
    total_objects: usize,
}

impl HasHole for Slab {
    fn hole(&mut self) -> &mut ListNode {
        &mut self.hole
    }
}
