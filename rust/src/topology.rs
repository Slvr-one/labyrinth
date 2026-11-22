//! Validated connected, simple, undirected carrier storage.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidSize,
    InvalidIndex,
    InvalidCarrier,
    Disconnected,
    InvalidChoice,
    InvalidForest,
    InvalidTree,
    InvalidTransition,
    InsufficientWorkspace,
    Overflow,
    StaleEpoch,
    StaleRevision,
    Occupied,
    InvalidGeometry,
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::InvalidSize => "invalid size",
            Self::InvalidIndex => "invalid index",
            Self::InvalidCarrier => "invalid carrier",
            Self::Disconnected => "disconnected carrier",
            Self::InvalidChoice => "random choice outside its bound",
            Self::InvalidForest => "invalid required forest",
            Self::InvalidTree => "invalid rooted tree",
            Self::InvalidTransition => "invalid tree transition",
            Self::InsufficientWorkspace => "insufficient workspace",
            Self::Overflow => "size or arithmetic overflow",
            Self::StaleEpoch => "stale epoch",
            Self::StaleRevision => "stale revision",
            Self::Occupied => "occupied passage",
            Self::InvalidGeometry => "invalid geometry",
        };
        formatter.write_str(message)
    }
}

impl core::error::Error for Error {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub u: usize,
    pub v: usize,
}

impl Edge {
    pub fn new(u: usize, v: usize) -> Self {
        if u <= v {
            Self { u, v }
        } else {
            Self { u: v, v: u }
        }
    }
}

pub(crate) fn check_storage(count: usize, element_bytes: usize) -> Result<(), Error> {
    let bytes = count.checked_mul(element_bytes).ok_or(Error::Overflow)?;
    if bytes > isize::MAX as usize {
        return Err(Error::Overflow);
    }
    Ok(())
}

pub(crate) fn count_edge(
    offsets: &mut [usize],
    cell_count: usize,
    edge: Edge,
) -> Result<(), Error> {
    if edge.u >= cell_count || edge.v >= cell_count {
        return Err(Error::InvalidIndex);
    }
    if edge.u == edge.v {
        return Err(Error::InvalidCarrier);
    }
    offsets[edge.u + 1] = offsets[edge.u + 1].checked_add(1).ok_or(Error::Overflow)?;
    offsets[edge.v + 1] = offsets[edge.v + 1].checked_add(1).ok_or(Error::Overflow)?;
    Ok(())
}

pub(crate) fn prefix_offsets(offsets: &mut [usize]) -> Result<(), Error> {
    let mut i = 1;
    let mut status = Ok(());
    while i < offsets.len() && status.is_ok() {
        match offsets[i].checked_add(offsets[i - 1]) {
            Some(sum) => offsets[i] = sum,
            None => status = Err(Error::Overflow),
        }
        i += 1;
    }
    status
}

fn validate_row_entry(
    offsets: &[usize],
    neighbors: &[usize],
    cell: usize,
    index: usize,
) -> Result<(), Error> {
    let neighbor = neighbors[index];
    if neighbor >= offsets.len() - 1 {
        return Err(Error::InvalidIndex);
    }
    if neighbor == cell {
        return Err(Error::InvalidCarrier);
    }
    let mut j = offsets[cell];
    while j < index && neighbors[j] != neighbor {
        j += 1;
    }
    if j < index {
        return Err(Error::InvalidCarrier);
    }
    j = offsets[neighbor];
    while j < offsets[neighbor + 1] && neighbors[j] != cell {
        j += 1;
    }
    if j == offsets[neighbor + 1] {
        return Err(Error::InvalidCarrier);
    }
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
pub struct Carrier {
    offsets: Vec<usize>,
    neighbors: Vec<usize>,
    edges: Vec<Edge>,
}

impl Carrier {
    /// Input order determines each reciprocal row's order.
    /// Validation runs through `from_csr`, so it costs O(sum of squared row degrees).
    ///
    /// # Errors
    /// Rejects empty, overflowing, malformed, duplicate, or disconnected input.
    pub fn from_edges(cell_count: usize, edges: &[Edge]) -> Result<Self, Error> {
        if cell_count == 0 {
            return Err(Error::InvalidSize);
        }
        let offset_count = cell_count.checked_add(1).ok_or(Error::Overflow)?;
        let adjacency_count = edges.len().checked_mul(2).ok_or(Error::Overflow)?;
        check_storage(offset_count, const { core::mem::size_of::<usize>() })?;
        check_storage(adjacency_count, const { core::mem::size_of::<usize>() })?;
        check_storage(edges.len(), const { core::mem::size_of::<Edge>() })?;
        let mut offsets = vec![0usize; offset_count];
        let mut i = 0;
        let mut status = Ok(());
        while i < edges.len() && status.is_ok() {
            status = count_edge(&mut offsets, cell_count, edges[i]);
            i += 1;
        }
        status?;
        prefix_offsets(&mut offsets)?;
        let mut next = vec![0usize; cell_count];
        i = 0;
        while i < cell_count {
            next[i] = offsets[i];
            i += 1;
        }
        let mut neighbors = vec![0usize; adjacency_count];
        i = 0;
        while i < edges.len() {
            let edge = edges[i];
            neighbors[next[edge.u]] = edge.v;
            next[edge.u] += 1;
            neighbors[next[edge.v]] = edge.u;
            next[edge.v] += 1;
            i += 1;
        }
        Self::from_csr(offsets, neighbors)
    }

    /// Rows retain their supplied order; invalid storage is never indexed first.
    /// Validation costs O(sum of squared row degrees); intended for bounded-degree carriers.
    ///
    /// # Errors
    /// Rejects empty, malformed, asymmetric, nonsimple, or disconnected storage.
    pub fn from_csr(offsets: Vec<usize>, neighbors: Vec<usize>) -> Result<Self, Error> {
        if offsets.len() < 2 {
            return Err(Error::InvalidSize);
        }
        let n = offsets.len() - 1;
        if offsets[0] != 0 || offsets[n] != neighbors.len() {
            return Err(Error::InvalidCarrier);
        }
        let mut u = 0;
        let mut valid_offsets = true;
        while u < n && valid_offsets {
            valid_offsets = offsets[u] <= offsets[u + 1] && offsets[u + 1] <= neighbors.len();
            u += 1;
        }
        if !valid_offsets {
            return Err(Error::InvalidCarrier);
        }
        let mut status = Ok(());
        u = 0;
        while u < n && status.is_ok() {
            let mut i = offsets[u];
            while i < offsets[u + 1] && status.is_ok() {
                status = validate_row_entry(&offsets, &neighbors, u, i);
                i += 1;
            }
            u += 1;
        }
        status?;
        check_storage(n, const { core::mem::size_of::<usize>() })?;
        let mut seen = vec![false; n];
        let mut stack = vec![0usize; n];
        let mut depth = 1;
        let mut reached = 1;
        seen[0] = true;
        while depth > 0 {
            depth -= 1;
            u = stack[depth];
            let mut i = offsets[u];
            while i < offsets[u + 1] {
                let v = neighbors[i];
                if !seen[v] {
                    seen[v] = true;
                    stack[depth] = v;
                    depth += 1;
                    reached += 1;
                }
                i += 1;
            }
        }
        if reached != n {
            return Err(Error::Disconnected);
        }
        check_storage(neighbors.len() / 2, const { core::mem::size_of::<Edge>() })?;
        let mut edges = vec![Edge::new(0, 0); neighbors.len() / 2];
        let mut count = 0;
        u = 0;
        while u < n {
            let mut i = offsets[u];
            while i < offsets[u + 1] {
                let v = neighbors[i];
                if u < v {
                    edges[count] = Edge::new(u, v);
                    count += 1;
                }
                i += 1;
            }
            u += 1;
        }
        Ok(Self {
            offsets,
            neighbors,
            edges,
        })
    }

    pub fn len(&self) -> usize {
        self.offsets.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Invalid cells have an empty row.
    pub fn neighbors(&self, cell: usize) -> &[usize] {
        if cell >= self.len() {
            return &[];
        }
        &self.neighbors[self.offsets[cell]..self.offsets[cell + 1]]
    }

    pub fn contains_edge(&self, edge: Edge) -> bool {
        if edge.u >= self.len() || edge.v >= self.len() || edge.u == edge.v {
            return false;
        }
        let row = self.neighbors(edge.u);
        let mut i = 0;
        while i < row.len() && row[i] != edge.v {
            i += 1;
        }
        i < row.len()
    }

    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    pub(crate) fn storage(&self) -> (&[usize], &[usize]) {
        (&self.offsets, &self.neighbors)
    }
}
