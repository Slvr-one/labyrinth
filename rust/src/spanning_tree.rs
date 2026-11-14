//! Depth-first construction and atomic, allocation-free parent-path edits.

use alloc::vec;
use alloc::vec::Vec;

use crate::topology::{check_storage, count_edge, prefix_offsets, Carrier, Edge, Error};
use crate::tree::Rng;

#[derive(Debug, Clone, Copy)]
struct Frame {
    cell: usize,
    next: usize,
    remaining: usize,
}

#[derive(Debug)]
pub struct Workspace {
    seen: Vec<bool>,
    frames: Vec<Frame>,
    path: Vec<usize>,
    parents: Vec<usize>,
    incoming: Vec<usize>,
    edit_slots: Vec<usize>,
    edit_nodes: Vec<usize>,
    edit_count: usize,
    edge_capacity: usize,
}

impl Workspace {
    /// Scratch is initialized once; mutations reuse only touched edit slots.
    ///
    /// # Errors
    /// Rejects zero cells and storage sizes exceeding addressable allocation bounds.
    pub fn new(cell_count: usize, edge_count: usize) -> Result<Self, Error> {
        if cell_count == 0 {
            return Err(Error::InvalidSize);
        }
        check_storage(cell_count, const { core::mem::size_of::<usize>() })?;
        check_storage(cell_count, const { core::mem::size_of::<Frame>() })?;
        check_storage(edge_count, const { core::mem::size_of::<Edge>() })?;
        let adjacency_count = edge_count.checked_mul(2).ok_or(Error::Overflow)?;
        check_storage(adjacency_count, const { core::mem::size_of::<usize>() })?;
        Ok(Self {
            seen: vec![false; cell_count],
            frames: vec![
                Frame {
                    cell: 0,
                    next: 0,
                    remaining: 0
                };
                cell_count
            ],
            path: vec![0; cell_count],
            parents: vec![0; cell_count],
            incoming: vec![0; cell_count],
            edit_slots: vec![usize::MAX; cell_count],
            edit_nodes: vec![0; cell_count],
            edit_count: 0,
            edge_capacity: edge_count,
        })
    }

    fn ensure(&self, cells: usize, edges: usize) -> Result<(), Error> {
        if cells > self.path.len() || edges > self.edge_capacity {
            return Err(Error::InsufficientWorkspace);
        }
        Ok(())
    }

    fn clear_edits(&mut self) {
        let mut i = 0;
        while i < self.edit_count {
            self.edit_slots[self.edit_nodes[i]] = usize::MAX;
            i += 1;
        }
        self.edit_count = 0;
    }

    fn parent(&self, published: &[usize], cell: usize) -> usize {
        let slot = self.edit_slots[cell];
        if slot == usize::MAX {
            published[cell]
        } else {
            self.parents[slot]
        }
    }

    fn set_parent(&mut self, cell: usize, parent: usize) {
        let mut slot = self.edit_slots[cell];
        if slot == usize::MAX {
            slot = self.edit_count;
            self.edit_count += 1;
            self.edit_slots[cell] = slot;
            self.edit_nodes[slot] = cell;
        }
        self.parents[slot] = parent;
    }
}

fn enter<R: Rng>(offsets: &[usize], cell: usize, rng: &mut R) -> Result<Frame, Error> {
    let degree = offsets[cell + 1] - offsets[cell];
    let mut next = offsets[cell];
    if degree > 0 {
        let choice = rng.next_below(degree);
        if choice >= degree {
            return Err(Error::InvalidChoice);
        }
        next += choice;
    }
    Ok(Frame {
        cell,
        next,
        remaining: degree,
    })
}

fn depth_first<R: Rng>(
    offsets: &[usize],
    neighbors: &[usize],
    root: usize,
    rng: &mut R,
    work: &mut Workspace,
) -> Result<(), Error> {
    let n = offsets.len() - 1;
    work.clear_edits();
    let mut i = 0;
    while i < n {
        work.seen[i] = false;
        work.parents[i] = root;
        work.incoming[i] = 0;
        i += 1;
    }
    work.frames[0] = enter(offsets, root, rng)?;
    work.seen[root] = true;
    let mut reached = 1;
    let mut depth = 1;
    let mut status = Ok(());
    while depth > 0 && status.is_ok() {
        let frame = work.frames[depth - 1];
        if frame.remaining == 0 {
            depth -= 1;
        } else {
            let slot = frame.next;
            let neighbor = neighbors[slot];
            let mut next = slot + 1;
            if next == offsets[frame.cell + 1] {
                next = offsets[frame.cell];
            }
            work.frames[depth - 1].next = next;
            work.frames[depth - 1].remaining -= 1;
            if !work.seen[neighbor] {
                match enter(offsets, neighbor, rng) {
                    Ok(child_frame) => {
                        work.parents[neighbor] = frame.cell;
                        work.incoming[neighbor] = slot;
                        work.seen[neighbor] = true;
                        work.frames[depth] = child_frame;
                        depth += 1;
                        reached += 1;
                    }
                    Err(error) => status = Err(error),
                }
            }
        }
    }
    status?;
    if reached != n {
        return Err(Error::Disconnected);
    }
    Ok(())
}

fn representative(links: &[usize], start: usize) -> usize {
    let mut cell = start;
    while links[cell] != cell {
        cell = links[cell];
    }
    cell
}

fn join_required(
    carrier: &Carrier,
    links: &mut [usize],
    sizes: &mut [usize],
    edge: Edge,
) -> Result<(), Error> {
    if !carrier.contains_edge(edge) {
        return Err(Error::InvalidForest);
    }
    let mut u = representative(links, edge.u);
    let mut v = representative(links, edge.v);
    if u == v {
        return Err(Error::InvalidForest);
    }
    if sizes[u] < sizes[v] {
        core::mem::swap(&mut u, &mut v);
    }
    links[v] = u;
    sizes[u] += sizes[v];
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
pub struct Tree {
    parents: Vec<usize>,
    root: usize,
}

impl Tree {
    /// Each entered nonisolated row consumes exactly one checked cyclic offset.
    ///
    /// # Errors
    /// Rejects an invalid root, insufficient scratch, or an out-of-range choice.
    pub fn dfs<R: Rng>(
        carrier: &Carrier,
        root: usize,
        rng: &mut R,
        work: &mut Workspace,
    ) -> Result<Self, Error> {
        if root >= carrier.len() {
            return Err(Error::InvalidIndex);
        }
        work.ensure(carrier.len(), carrier.edges().len())?;
        let (offsets, neighbors) = carrier.storage();
        depth_first(offsets, neighbors, root, rng, work)?;
        let mut parents = vec![root; carrier.len()];
        let mut i = 0;
        while i < parents.len() {
            parents[i] = work.parents[i];
            i += 1;
        }
        Ok(Self { parents, root })
    }

    /// Parallel quotient edges retain distinct original-edge witnesses in carrier edge order.
    ///
    /// # Errors
    /// Rejects invalid roots, noncarrier or cyclic required edges, insufficient scratch,
    /// overflowing storage, and out-of-range quotient choices.
    pub fn scene_dfs<R: Rng>(
        carrier: &Carrier,
        required: &[Edge],
        root: usize,
        rng: &mut R,
        work: &mut Workspace,
    ) -> Result<Self, Error> {
        let n = carrier.len();
        if root >= n {
            return Err(Error::InvalidIndex);
        }
        work.ensure(n, carrier.edges().len())?;
        if required.len() >= n {
            return Err(Error::InvalidForest);
        }
        let mut links = vec![0usize; n];
        let mut sizes = vec![1usize; n];
        let mut i = 0;
        while i < n {
            links[i] = i;
            i += 1;
        }
        i = 0;
        let mut status = Ok(());
        while i < required.len() && status.is_ok() {
            status = join_required(carrier, &mut links, &mut sizes, required[i]);
            i += 1;
        }
        status?;
        let mut components = vec![0usize; n];
        let mut labels = vec![n; n];
        let mut component_count = 0usize;
        i = 0;
        while i < n {
            let representative = representative(&links, i);
            if labels[representative] == n {
                labels[representative] = component_count;
                component_count += 1;
            }
            components[i] = labels[representative];
            i += 1;
        }
        let offset_count = component_count.checked_add(1).ok_or(Error::Overflow)?;
        check_storage(offset_count, const { core::mem::size_of::<usize>() })?;
        let mut offsets = vec![0usize; offset_count];
        let edges = carrier.edges();
        i = 0;
        while i < edges.len() && status.is_ok() {
            let u = components[edges[i].u];
            let v = components[edges[i].v];
            if u != v {
                status = count_edge(&mut offsets, component_count, Edge::new(u, v));
            }
            i += 1;
        }
        status?;
        prefix_offsets(&mut offsets)?;
        let adjacency_count = offsets[component_count];
        check_storage(adjacency_count, const { core::mem::size_of::<usize>() })?;
        check_storage(adjacency_count, const { core::mem::size_of::<Edge>() })?;
        let mut neighbors = vec![0usize; adjacency_count];
        let mut witnesses = vec![Edge::new(0, 0); adjacency_count];
        let mut next = vec![0usize; component_count];
        i = 0;
        while i < component_count {
            next[i] = offsets[i];
            i += 1;
        }
        i = 0;
        while i < edges.len() {
            let edge = edges[i];
            let u = components[edge.u];
            let v = components[edge.v];
            if u != v {
                neighbors[next[u]] = v;
                witnesses[next[u]] = edge;
                next[u] += 1;
                neighbors[next[v]] = u;
                witnesses[next[v]] = edge;
                next[v] += 1;
            }
            i += 1;
        }
        let quotient_root = components[root];
        depth_first(&offsets, &neighbors, quotient_root, rng, work)?;
        check_storage(n - 1, const { core::mem::size_of::<Edge>() })?;
        let mut selected = vec![Edge::new(0, 0); n - 1];
        i = 0;
        while i < required.len() {
            selected[i] = Edge::new(required[i].u, required[i].v);
            i += 1;
        }
        let mut selected_count = required.len();
        i = 0;
        while i < component_count {
            if i != quotient_root {
                selected[selected_count] = witnesses[work.incoming[i]];
                selected_count += 1;
            }
            i += 1;
        }
        let expanded = Carrier::from_edges(n, &selected)?;
        let mut parents = vec![root; n];
        i = 0;
        while i < n {
            work.seen[i] = false;
            i += 1;
        }
        work.seen[root] = true;
        work.path[0] = root;
        let mut depth = 1;
        while depth > 0 {
            depth -= 1;
            let cell = work.path[depth];
            let row = expanded.neighbors(cell);
            i = 0;
            while i < row.len() {
                let neighbor = row[i];
                if !work.seen[neighbor] {
                    work.seen[neighbor] = true;
                    parents[neighbor] = cell;
                    work.path[depth] = neighbor;
                    depth += 1;
                }
                i += 1;
            }
        }
        Ok(Self { parents, root })
    }

    pub fn parents(&self) -> &[usize] {
        &self.parents
    }

    pub fn root(&self) -> usize {
        self.root
    }

    pub fn has_edge(&self, edge: Edge) -> bool {
        edge.u < self.parents.len()
            && edge.v < self.parents.len()
            && edge.u != edge.v
            && (self.parents[edge.u] == edge.v || self.parents[edge.v] == edge.u)
    }

    /// Only the old-to-new root path changes orientation.
    ///
    /// # Errors
    /// Rejects invalid roots, insufficient scratch, and malformed parent paths before writing.
    pub fn reroot(&mut self, new_root: usize, work: &mut Workspace) -> Result<(), Error> {
        let n = self.parents.len();
        if new_root >= n {
            return Err(Error::InvalidIndex);
        }
        work.ensure(n, 0)?;
        let mut cell = new_root;
        let mut count = 0;
        while cell < n && count < n && cell != self.root {
            work.path[count] = cell;
            count += 1;
            cell = self.parents[cell];
        }
        if cell >= n || count >= n {
            return Err(Error::InvalidTree);
        }
        work.path[count] = cell;
        count += 1;
        let mut i = 1;
        while i < count {
            self.parents[work.path[i]] = work.path[i - 1];
            i += 1;
        }
        self.parents[new_root] = new_root;
        self.root = new_root;
        Ok(())
    }

    /// The supplied edge must cross the components created by removing the child's parent edge.
    ///
    /// # Errors
    /// Rejects root cuts, invalid IDs, incompatible carriers, insufficient scratch,
    /// and attachments within one cut component without publishing any edits.
    pub fn exchange(
        &mut self,
        carrier: &Carrier,
        cut_child: usize,
        attach: Edge,
        work: &mut Workspace,
    ) -> Result<(), Error> {
        if cut_child >= self.parents.len() {
            return Err(Error::InvalidIndex);
        }
        if cut_child == self.root {
            return Err(Error::InvalidTransition);
        }
        let cut = Edge::new(cut_child, self.parents[cut_child]);
        self.edit_edges(carrier, &[cut], &[attach], work)
    }

    /// A complete batch is checked in a sparse virtual-parent overlay before publication.
    ///
    /// # Errors
    /// Rejects unequal counts, duplicate edits, missing removals, existing additions
    /// not removed by this batch, noncarrier edges, cycles, disconnected results,
    /// incompatible carriers, and insufficient scratch. The root remains unchanged.
    pub fn edit_edges(
        &mut self,
        carrier: &Carrier,
        remove: &[Edge],
        add: &[Edge],
        work: &mut Workspace,
    ) -> Result<(), Error> {
        let n = self.parents.len();
        work.ensure(n, carrier.edges().len())?;
        self.check_carrier(carrier)?;
        if remove.len() != add.len() || remove.len() >= n {
            return Err(Error::InvalidTransition);
        }
        let mut i = 0;
        let mut status = Ok(());
        while i < remove.len() && status.is_ok() {
            status = self.check_edit(carrier, remove, add, i);
            i += 1;
        }
        status?;
        work.clear_edits();
        i = 0;
        while i < remove.len() {
            let edge = remove[i];
            let child = if self.parents[edge.u] == edge.v {
                edge.u
            } else {
                edge.v
            };
            work.set_parent(child, child);
            i += 1;
        }
        i = 0;
        while i < add.len() && status.is_ok() {
            status = self.attach_virtual(add[i], work);
            i += 1;
        }
        status?;
        i = 0;
        while i < work.edit_count {
            self.parents[work.edit_nodes[i]] = work.parents[i];
            i += 1;
        }
        Ok(())
    }

    fn check_edit(
        &self,
        carrier: &Carrier,
        remove: &[Edge],
        add: &[Edge],
        index: usize,
    ) -> Result<(), Error> {
        let n = self.parents.len();
        let removal = Edge::new(remove[index].u, remove[index].v);
        let addition = Edge::new(add[index].u, add[index].v);
        if removal.u >= n || removal.v >= n || addition.u >= n || addition.v >= n {
            return Err(Error::InvalidIndex);
        }
        if !self.has_edge(removal) || !carrier.contains_edge(addition) {
            return Err(Error::InvalidTransition);
        }
        let mut duplicate = false;
        let mut j = 0;
        while j < index && !duplicate {
            duplicate = Edge::new(remove[j].u, remove[j].v) == removal
                || Edge::new(add[j].u, add[j].v) == addition;
            j += 1;
        }
        if duplicate {
            return Err(Error::InvalidTransition);
        }
        if self.has_edge(addition) {
            j = 0;
            while j < remove.len() && Edge::new(remove[j].u, remove[j].v) != addition {
                j += 1;
            }
            if j == remove.len() {
                return Err(Error::InvalidTransition);
            }
        }
        Ok(())
    }

    fn attach_virtual(&self, edge: Edge, work: &mut Workspace) -> Result<(), Error> {
        let n = self.parents.len();
        let u_root = self.virtual_root(edge.u, work)?;
        let v_root = self.virtual_root(edge.v, work)?;
        if u_root == v_root {
            return Err(Error::InvalidTransition);
        }
        let (inside, outside, component_root) = if u_root == self.root {
            (edge.v, edge.u, v_root)
        } else {
            (edge.u, edge.v, u_root)
        };
        let mut cell = inside;
        let mut count = 0;
        while cell < n && count < n && cell != component_root {
            work.path[count] = cell;
            count += 1;
            cell = work.parent(&self.parents, cell);
        }
        if cell >= n || count >= n {
            return Err(Error::InvalidTree);
        }
        work.path[count] = cell;
        count += 1;
        let mut j = 1;
        while j < count {
            work.set_parent(work.path[j], work.path[j - 1]);
            j += 1;
        }
        work.set_parent(inside, outside);
        Ok(())
    }

    fn virtual_root(&self, start: usize, work: &Workspace) -> Result<usize, Error> {
        let mut cell = start;
        let mut steps = 0;
        let mut found = false;
        while steps < self.parents.len() && cell < self.parents.len() && !found {
            let parent = work.parent(&self.parents, cell);
            if parent == cell {
                found = true;
            } else {
                cell = parent;
            }
            steps += 1;
        }
        if found {
            Ok(cell)
        } else {
            Err(Error::InvalidTree)
        }
    }

    fn check_carrier(&self, carrier: &Carrier) -> Result<(), Error> {
        if self.parents.len() != carrier.len()
            || self.root >= self.parents.len()
            || self.parents[self.root] != self.root
        {
            return Err(Error::InvalidTree);
        }
        let mut cell = 0;
        let mut valid = true;
        while cell < self.parents.len() && valid {
            valid = cell == self.root || carrier.contains_edge(Edge::new(cell, self.parents[cell]));
            cell += 1;
        }
        if valid {
            Ok(())
        } else {
            Err(Error::InvalidTree)
        }
    }

    /// Checks carrier membership and bounded root reachability of every parent chain.
    ///
    /// # Errors
    /// Rejects size mismatches, invalid roots or parents, noncarrier edges, and cycles.
    pub fn validate(&self, carrier: &Carrier) -> Result<(), Error> {
        self.check_carrier(carrier)?;
        let n = self.parents.len();
        let mut start = 0;
        let mut valid = true;
        while start < n && valid {
            let mut cell = start;
            let mut steps = 0;
            while cell != self.root && cell < n && steps < n {
                cell = self.parents[cell];
                steps += 1;
            }
            valid = cell == self.root;
            start += 1;
        }
        if valid {
            Ok(())
        } else {
            Err(Error::InvalidTree)
        }
    }
}
