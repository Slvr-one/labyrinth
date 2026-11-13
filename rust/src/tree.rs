#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidIndex,
    SelfParent,
    Cycle,
}

/// Randomness adapter: integer-only, returns a value in `0..bound`.
pub trait Rng {
    fn next_below(&mut self, bound: usize) -> usize;
}

/// Follows parent links from `start` for at most `parents.len()` steps and
/// reports whether `child` is reached.
pub fn reaches(parents: &[usize], child: usize, start: usize) -> bool {
    let n = parents.len();
    let mut cur = start;
    let mut steps = 0usize;
    while steps < n {
        if cur == child {
            return true;
        }
        cur = parents[cur];
        steps += 1;
    }
    false
}

/// Sets `parents[child] = new_parent` unless that is invalid or creates a cycle.
pub fn set_parent(parents: &mut [usize], child: usize, new_parent: usize) -> Result<(), Error> {
    let n = parents.len();
    if child >= n || new_parent >= n {
        return Err(Error::InvalidIndex);
    }
    if child == new_parent {
        return Err(Error::SelfParent);
    }
    if reaches(parents, child, new_parent) {
        return Err(Error::Cycle);
    }
    parents[child] = new_parent;
    Ok(())
}

/// Chooses the new parent through the randomness adapter, then applies `set_parent`.
pub fn random_reparent<R: Rng>(
    parents: &mut [usize],
    child: usize,
    rng: &mut R,
) -> Result<(), Error> {
    let n = parents.len();
    if n == 0 {
        return Err(Error::InvalidIndex);
    }
    let candidate = rng.next_below(n);
    set_parent(parents, child, candidate)
}
