//! Checked integer geometry and retained rectangular cells.

use crate::topology::{check_storage, Error};
use alloc::vec;
use alloc::vec::Vec;

/// Coordinates are bounded so squared distances and interpolation fit in i64.
pub const COORD_LIMIT: i32 = 1_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    pub fn validate(self) -> Result<(), Error> {
        if self.x < -COORD_LIMIT
            || self.x > COORD_LIMIT
            || self.y < -COORD_LIMIT
            || self.y > COORD_LIMIT
        {
            return Err(Error::InvalidGeometry);
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rect {
    pub min: Point,
    pub max: Point,
}

impl Rect {
    pub fn validate(self) -> Result<(), Error> {
        self.min.validate()?;
        self.max.validate()?;
        if self.min.x >= self.max.x || self.min.y >= self.max.y {
            return Err(Error::InvalidGeometry);
        }
        Ok(())
    }

    pub fn contains(self, other: Self) -> bool {
        self.min.x <= other.min.x
            && self.min.y <= other.min.y
            && self.max.x >= other.max.x
            && self.max.y >= other.max.y
    }

    pub fn contains_point(self, point: Point) -> bool {
        point.x >= self.min.x
            && point.x <= self.max.x
            && point.y >= self.min.y
            && point.y <= self.max.y
    }

    pub fn intersects(self, other: Self) -> bool {
        self.min.x <= other.max.x
            && other.min.x <= self.max.x
            && self.min.y <= other.max.y
            && other.min.y <= self.max.y
    }

    pub fn union(self, other: Self) -> Self {
        Self {
            min: Point {
                x: self.min.x.min(other.min.x),
                y: self.min.y.min(other.min.y),
            },
            max: Point {
                x: self.max.x.max(other.max.x),
                y: self.max.y.max(other.max.y),
            },
        }
    }

    pub fn expand(self, margin: i32) -> Result<Self, Error> {
        if margin < 0 {
            return Err(Error::InvalidGeometry);
        }
        let result = Self {
            min: Point {
                x: self.min.x.checked_sub(margin).ok_or(Error::Overflow)?,
                y: self.min.y.checked_sub(margin).ok_or(Error::Overflow)?,
            },
            max: Point {
                x: self.max.x.checked_add(margin).ok_or(Error::Overflow)?,
                y: self.max.y.checked_add(margin).ok_or(Error::Overflow)?,
            },
        };
        result.validate()?;
        Ok(result)
    }

    pub(crate) fn center(self) -> Point {
        Point {
            x: self.min.x + (self.max.x - self.min.x) / 2,
            y: self.min.y + (self.max.y - self.min.y) / 2,
        }
    }

    pub fn between(a: Point, b: Point, margin: i32) -> Result<Self, Error> {
        if margin <= 0 {
            return Err(Error::InvalidGeometry);
        }
        Self {
            min: Point {
                x: a.x.min(b.x),
                y: a.y.min(b.y),
            },
            max: Point {
                x: a.x.max(b.x),
                y: a.y.max(b.y),
            },
        }
        .expand(margin)
    }

    pub(crate) fn touches_disk(self, center: Point, radius: i32) -> bool {
        let x = center.x.clamp(self.min.x, self.max.x);
        let y = center.y.clamp(self.min.y, self.max.y);
        let dx = i64::from(center.x) - i64::from(x);
        let dy = i64::from(center.y) - i64::from(y);
        dx * dx + dy * dy <= i64::from(radius) * i64::from(radius)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Geometry {
    pub viewport: Rect,
    pub obstacles: Vec<Rect>,
    pub walker_radius: i32,
    pub clearance: i32,
}

impl Geometry {
    pub fn validate(&self) -> Result<(), Error> {
        self.viewport.validate()?;
        if self.walker_radius <= 0 || self.clearance < 0 {
            return Err(Error::InvalidGeometry);
        }
        self.margin()?;
        let mut status = Ok(());
        let mut i = 0;
        while i < self.obstacles.len() && status.is_ok() {
            status = self.obstacles[i].validate();
            i += 1;
        }
        status
    }

    pub fn margin(&self) -> Result<i32, Error> {
        if self.walker_radius <= 0 || self.clearance < 0 {
            return Err(Error::InvalidGeometry);
        }
        let margin = self
            .walker_radius
            .checked_add(self.clearance)
            .ok_or(Error::Overflow)?;
        let margin = margin.checked_add(2).ok_or(Error::Overflow)?;
        if margin > COORD_LIMIT {
            return Err(Error::InvalidGeometry);
        }
        Ok(margin)
    }

    pub fn check(&self, swept: Rect) -> Result<(), Error> {
        swept.validate()?;
        if !self.viewport.contains(swept) {
            return Err(Error::InvalidGeometry);
        }
        let mut blocked = false;
        let mut i = 0;
        while i < self.obstacles.len() && !blocked {
            blocked = swept.intersects(self.obstacles[i]);
            i += 1;
        }
        if blocked {
            Err(Error::InvalidGeometry)
        } else {
            Ok(())
        }
    }
}

/// `Layout::new` allocates and scans `columns * rows` slots, so memory and time grow with the
/// product. Only sizes above `isize::MAX` bytes are rejected; the caller bounds the grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GridSpec {
    pub columns: usize,
    pub rows: usize,
    pub origin: Point,
    pub cell_size: i32,
}

#[derive(Debug)]
pub struct Grid {
    spec: GridSpec,
    ids: Vec<Option<usize>>,
}

impl Grid {
    pub(crate) fn new(spec: GridSpec) -> Result<Self, Error> {
        spec.origin.validate()?;
        if spec.columns == 0 || spec.rows == 0 || spec.cell_size <= 0 {
            return Err(Error::InvalidSize);
        }
        let count = spec.columns.checked_mul(spec.rows).ok_or(Error::Overflow)?;
        check_storage(count, const { core::mem::size_of::<Option<usize>>() })?;
        if spec.columns > i32::MAX as usize {
            return Err(Error::Overflow);
        }
        let width = (spec.columns as i32)
            .checked_mul(spec.cell_size)
            .ok_or(Error::Overflow)?;
        if spec.rows > i32::MAX as usize {
            return Err(Error::Overflow);
        }
        let height = (spec.rows as i32)
            .checked_mul(spec.cell_size)
            .ok_or(Error::Overflow)?;
        Point {
            x: spec.origin.x.checked_add(width).ok_or(Error::Overflow)?,
            y: spec.origin.y.checked_add(height).ok_or(Error::Overflow)?,
        }
        .validate()?;
        Ok(Self {
            spec,
            ids: vec![None; count],
        })
    }

    pub fn cell(&self, column: usize, row: usize) -> Option<usize> {
        if column >= self.spec.columns || row >= self.spec.rows {
            return None;
        }
        self.ids[row * self.spec.columns + column]
    }

    pub fn spec(&self) -> GridSpec {
        self.spec
    }

    pub(crate) fn retain(&mut self, column: usize, row: usize, id: usize) {
        self.ids[row * self.spec.columns + column] = Some(id);
    }

    pub(crate) fn bounds(&self, column: usize, row: usize) -> Rect {
        let x = self.spec.origin.x + column as i32 * self.spec.cell_size;
        let y = self.spec.origin.y + row as i32 * self.spec.cell_size;
        Rect {
            min: Point { x, y },
            max: Point {
                x: x + self.spec.cell_size,
                y: y + self.spec.cell_size,
            },
        }
    }
}
