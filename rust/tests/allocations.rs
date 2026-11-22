use labyrinth_core::spanning_tree::{Tree, Workspace};
use labyrinth_core::topology::{Carrier, Edge};
use labyrinth_core::tree::Rng;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct CountingAllocator;

thread_local! {
    static TRACK: Cell<bool> = const { Cell::new(false) };
    static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
}

fn record_allocation() {
    let _ = TRACK.try_with(|track| {
        if track.get() {
            let _ = ALLOCATIONS.try_with(|count| count.set(count.get() + 1));
        }
    });
}

// Every allocation retains the System allocator's layout and ownership contract.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record_allocation();
        unsafe { System.realloc(pointer, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

struct First;
impl Rng for First {
    fn next_below(&mut self, _: usize) -> usize {
        0
    }
}

#[test]
fn repeated_path_reversal_and_atomic_edge_batches_allocate_nothing() {
    let path = [Edge::new(0, 1), Edge::new(1, 2), Edge::new(2, 3)];
    let carrier = Carrier::from_edges(4, &[path[0], path[1], path[2], Edge::new(0, 3)]).unwrap();
    let mut workspace = Workspace::new(4, carrier.edges().len()).unwrap();
    let mut tree = Tree::scene_dfs(&carrier, &path, 0, &mut First, &mut workspace).unwrap();
    ALLOCATIONS.with(|count| count.set(0));
    TRACK.with(|track| track.set(true));
    let result = (|| {
        for _ in 0..100 {
            tree.reroot(3, &mut workspace)?;
            tree.reroot(0, &mut workspace)?;
            tree.exchange(&carrier, 3, Edge::new(0, 3), &mut workspace)?;
            tree.edit_edges(
                &carrier,
                &[Edge::new(0, 3)],
                &[Edge::new(2, 3)],
                &mut workspace,
            )?;
        }
        Ok::<(), labyrinth_core::topology::Error>(())
    })();
    TRACK.with(|track| track.set(false));
    assert_eq!(result, Ok(()));
    assert_eq!(tree.parents(), &[0, 0, 1, 2]);
    assert_eq!(ALLOCATIONS.with(Cell::get), 0);
}
