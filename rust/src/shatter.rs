//! Shatter admission and presentation stages, separated from logical passage topology.

use crate::topology::Error;
use alloc::vec;
use alloc::vec::Vec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PatchId {
    pub epoch: u64,
    pub slot: usize,
    pub serial: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    Idle,
    Draining,
    Parked,
    Hidden,
    Scattered { until: u64 },
    Reforming { until: u64 },
}

#[derive(Debug)]
pub(crate) struct Patch {
    pub(crate) serial: u64,
    pub(crate) stage: Stage,
    pub(crate) cells: Vec<bool>,
}

impl Patch {
    pub(crate) fn new(cell_count: usize) -> Self {
        Self {
            serial: 0,
            stage: Stage::Idle,
            cells: vec![false; cell_count],
        }
    }

    pub(crate) fn contains(&self, cell: usize) -> bool {
        self.stage != Stage::Idle && cell < self.cells.len() && self.cells[cell]
    }

    pub(crate) fn validate(&self, id: PatchId) -> Result<(), Error> {
        if self.stage == Stage::Idle || self.serial != id.serial {
            return Err(Error::InvalidTransition);
        }
        Ok(())
    }
}
