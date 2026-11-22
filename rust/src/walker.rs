//! Cell-local ownership and held-frame crossing interpolation.

use crate::grid::{Point, Rect};
use crate::polar::{angle_delta, normalize};
use crate::topology::{Edge, Error};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stamp {
    pub epoch: u64,
    pub revision: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reservation {
    pub epoch: u64,
    pub walker: usize,
    pub serial: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalPose {
    Cartesian(Point),
    Polar {
        circle: usize,
        radius: i32,
        angle: i32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Path {
    Cartesian {
        from: Point,
        to: Point,
    },
    Polar {
        circle: usize,
        from_radius: i32,
        to_radius: i32,
        from_angle: i32,
        doorway_angle: i32,
        to_angle: i32,
    },
}

fn interpolate(from: i32, to: i32, elapsed: u64, duration: u64) -> i32 {
    from + (i64::from(to - from) * elapsed as i64 / duration as i64) as i32
}

fn interpolate_angle(from: i32, to: i32, elapsed: u64, duration: u64) -> i32 {
    normalize(from + (i64::from(angle_delta(from, to)) * elapsed as i64 / duration as i64) as i32)
}

impl Path {
    pub(crate) fn pose(self, elapsed: u32, duration: u32) -> LocalPose {
        let elapsed = u64::from(elapsed);
        let duration = u64::from(duration);
        match self {
            Self::Cartesian { from, to } => LocalPose::Cartesian(Point {
                x: interpolate(from.x, to.x, elapsed, duration),
                y: interpolate(from.y, to.y, elapsed, duration),
            }),
            Self::Polar {
                circle,
                from_radius,
                to_radius,
                from_angle,
                doorway_angle,
                to_angle,
            } => {
                let phase = elapsed * 3;
                let (radius, angle) = if phase < duration {
                    (
                        from_radius,
                        interpolate_angle(from_angle, doorway_angle, phase, duration),
                    )
                } else if phase < duration * 2 {
                    (
                        interpolate(from_radius, to_radius, phase - duration, duration),
                        doorway_angle,
                    )
                } else {
                    (
                        to_radius,
                        interpolate_angle(doorway_angle, to_angle, phase - duration * 2, duration),
                    )
                };
                LocalPose::Polar {
                    circle,
                    radius,
                    angle,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Holds {
    pub(crate) ids: [usize; 4],
    pub(crate) count: usize,
}

impl Holds {
    pub(crate) fn new() -> Self {
        Self {
            ids: [0; 4],
            count: 0,
        }
    }

    pub(crate) fn insert(&mut self, id: usize) -> Result<(), Error> {
        let mut slot = 0;
        while slot < self.count && self.ids[slot] != id {
            slot += 1;
        }
        if slot == self.count {
            if self.count == self.ids.len() {
                return Err(Error::InsufficientWorkspace);
            }
            self.ids[slot] = id;
            self.count += 1;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Crossing {
    pub source: usize,
    pub target: usize,
    pub elapsed: u32,
    pub duration: u32,
    pub reservation: Reservation,
    pub corridor: Rect,
    pub(crate) path: Path,
    pub(crate) target_pose: LocalPose,
    pub(crate) holds: Holds,
}

impl Crossing {
    pub fn edge(self) -> Edge {
        Edge::new(self.source, self.target)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WalkerState {
    Ready,
    Crossing(Crossing),
    Parked,
    Hidden,
    Terminated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Walker {
    pub(crate) cell: usize,
    pub(crate) local: LocalPose,
    pub(crate) state: WalkerState,
}

impl Walker {
    pub fn cell(self) -> usize {
        self.cell
    }
    pub fn local_pose(self) -> LocalPose {
        self.local
    }
    pub fn state(self) -> WalkerState {
        self.state
    }
}

#[cfg(test)]
mod tests {
    use super::Holds;
    use crate::topology::Error;

    #[test]
    fn holds_deduplicate_and_preserve_full_storage_on_rejection() {
        let mut holds = Holds::new();
        holds.insert(0).expect("first transform");
        holds.insert(4).expect("second transform");
        holds.insert(0).expect("duplicate transform");
        assert_eq!(holds.count, 2);
        holds.insert(8).expect("third transform");
        holds.insert(12).expect("fourth transform");
        let full = holds;
        holds.insert(4).expect("duplicate in full storage");
        assert_eq!(holds, full);
        assert_eq!(holds.insert(16), Err(Error::InsufficientWorkspace));
        assert_eq!(holds, full);
        assert_eq!(holds.ids, [0, 4, 8, 12]);
    }
}
