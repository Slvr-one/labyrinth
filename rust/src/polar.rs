//! Integer polar embedding shared by walls, doorway bounds, and local walker poses.
// The adapter uses the shared fixed-point projection, outward obstacles, and an inward viewport.
//! Spinning admission conservatively reserves one-unit sweep clearance across adjacent rings.
//! These radius-dependent sufficient bounds may reject viable unequal partitions; no fixed sector cap applies.

use crate::grid::{Point, Rect, COORD_LIMIT};
use crate::topology::Error;
use alloc::vec::Vec;

pub const TURN: i32 = 4096;
const SCALE: i64 = 1 << 30;
const CORDIC_GAIN: i64 = 652_032_874;
const ATAN: [i64; 31] = [
    536_870_912,
    316_933_406,
    167_458_907,
    85_004_756,
    42_667_331,
    21_354_465,
    10_679_838,
    5_340_245,
    2_670_163,
    1_335_087,
    667_544,
    333_772,
    166_886,
    83_443,
    41_722,
    20_861,
    10_430,
    5_215,
    2_608,
    1_304,
    652,
    326,
    163,
    81,
    41,
    20,
    10,
    5,
    3,
    1,
    1,
];

pub fn normalize(angle: i32) -> i32 {
    angle.rem_euclid(TURN)
}

pub(crate) fn angle_delta(from: i32, to: i32) -> i32 {
    let difference = normalize(to - from);
    if difference > TURN / 2 {
        difference - TURN
    } else {
        difference
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Arc {
    pub start: i32,
    pub length: i32,
}

impl Arc {
    pub fn validate(self) -> Result<(), Error> {
        if self.start < 0 || self.start >= TURN || self.length <= 0 || self.length > TURN {
            return Err(Error::InvalidGeometry);
        }
        Ok(())
    }

    pub(crate) fn shifted(self, amount: i32) -> Self {
        Self {
            start: normalize(self.start + amount),
            length: self.length,
        }
    }

    pub(crate) fn swept(self, delta: i32) -> Self {
        if self.length + delta.abs() >= TURN {
            return Self {
                start: 0,
                length: TURN,
            };
        }
        Self {
            start: normalize(self.start + delta.min(0)),
            length: self.length + delta.abs(),
        }
    }

    pub(crate) fn middle(self) -> i32 {
        normalize(self.start + self.length / 2)
    }

    pub(crate) fn contains(self, angle: i32) -> bool {
        self.length == TURN || normalize(angle - self.start) <= self.length
    }
}

/// Finds a nonwrapping witness in the circular intersection of four intervals.
pub(crate) fn overlap(arcs: [Arc; 4], minimum: i32) -> Result<Arc, Error> {
    let mut best = Arc {
        start: 0,
        length: 0,
    };
    let mut i = 0;
    while i < arcs.len() {
        let start = arcs[i].start;
        let mut length = TURN;
        let mut j = 0;
        while j < arcs.len() {
            if arcs[j].length != TURN {
                let offset = normalize(start - arcs[j].start);
                if offset > arcs[j].length {
                    length = 0;
                    break;
                }
                length = length.min(arcs[j].length - offset);
            }
            j += 1;
        }
        if length > best.length {
            best = Arc { start, length };
        }
        i += 1;
    }
    if best.length < minimum {
        return Err(Error::InvalidGeometry);
    }
    Ok(best)
}

fn unit_vector(angle: i32) -> (i64, i64) {
    let angle = normalize(angle);
    let quadrant = angle / (TURN / 4);
    let local = angle % (TURN / 4);
    let mut x = if local == 0 { SCALE } else { CORDIC_GAIN };
    let mut y = 0;
    let mut residual = i64::from(local) << 20;
    let mut i = 0;
    while local != 0 && i < ATAN.len() {
        let previous_x = x;
        if residual >= 0 {
            x -= y >> i;
            y += previous_x >> i;
            residual -= ATAN[i];
        } else {
            x += y >> i;
            y -= previous_x >> i;
            residual += ATAN[i];
        }
        i += 1;
    }
    x = x.clamp(-SCALE, SCALE);
    y = y.clamp(-SCALE, SCALE);
    match quadrant {
        0 => (x, y),
        1 => (-y, x),
        2 => (-x, -y),
        _ => (y, -x),
    }
}

/// Q30 rotations share the geometry's two-coordinate-unit rounding guard.
pub(crate) fn point(center: Point, radius: i32, angle: i32) -> Point {
    let (x, y) = unit_vector(angle);
    Point {
        x: center.x + (i64::from(radius) * x / SCALE) as i32,
        y: center.y + (i64::from(radius) * y / SCALE) as i32,
    }
}

/// Renderers use this same checked, quantized circular projection for walls and occupants.
pub fn project(center: Point, radius: i32, angle: i32) -> Result<Point, Error> {
    center.validate()?;
    if !(0..=COORD_LIMIT).contains(&radius) {
        return Err(Error::InvalidGeometry);
    }
    let result = point(center, radius, angle);
    result.validate()?;
    Ok(result)
}

pub(crate) fn bounds(
    center: Point,
    inner: i32,
    outer: i32,
    arc: Arc,
    margin: i32,
) -> Result<Rect, Error> {
    let first = point(center, inner, arc.start);
    let mut result = Rect {
        min: first,
        max: first,
    };
    let mut i = 0;
    while i < 18 {
        let angle = if i == 16 {
            arc.start
        } else if i == 17 {
            normalize(arc.start + arc.length)
        } else {
            i * 256
        };
        if arc.contains(angle) {
            let mut r = 0;
            while r < 2 {
                let p = point(center, if r == 0 { inner } else { outer }, angle);
                result.min.x = result.min.x.min(p.x);
                result.min.y = result.min.y.min(p.y);
                result.max.x = result.max.x.max(p.x);
                result.max.y = result.max.y.max(p.y);
                r += 1;
            }
        }
        i += 1;
    }
    result.expand(margin)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Clockwise,
    Counterclockwise,
}

impl Direction {
    fn sign(self) -> i32 {
        match self {
            Self::Clockwise => 1,
            Self::Counterclockwise => -1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MotionMode {
    Spinning,
    /// A shared radial shear with a periodic, integer sampled sine phase.
    Twisting {
        amplitude: i32,
        max_relative: i32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolarSpec {
    pub center: Point,
    pub center_radius: i32,
    pub ring_width: i32,
    pub sectors: Vec<usize>,
    pub directions: Vec<Direction>,
    pub mode: MotionMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PortalSpec {
    pub circle: usize,
    pub column: usize,
    pub row: usize,
    pub mouth: Arc,
    pub band: i32,
}

#[derive(Debug)]
pub struct Circle {
    pub(crate) spec: PolarSpec,
    pub(crate) center_cell: usize,
    pub(crate) ring_starts: Vec<usize>,
    pub(crate) transform_start: usize,
    pub(crate) outer: i32,
}

impl Circle {
    pub(crate) fn new(
        spec: PolarSpec,
        center_cell: usize,
        transform_start: usize,
        margin: i32,
    ) -> Result<Self, Error> {
        spec.center.validate()?;
        if spec.sectors.is_empty()
            || spec.sectors.len() != spec.directions.len()
            || spec.center_radius < margin * 4
            || spec.ring_width < margin * 4
        {
            return Err(Error::InvalidGeometry);
        }
        if spec.sectors.len() > i32::MAX as usize {
            return Err(Error::Overflow);
        }
        let ring_count = spec.sectors.len() as i32;
        let outer = ring_count
            .checked_mul(spec.ring_width)
            .ok_or(Error::Overflow)?;
        let outer = outer
            .checked_add(spec.center_radius)
            .ok_or(Error::Overflow)?;
        if outer > COORD_LIMIT {
            return Err(Error::InvalidGeometry);
        }
        bounds(
            spec.center,
            0,
            outer,
            Arc {
                start: 0,
                length: TURN,
            },
            margin,
        )?;
        let mut ring_starts = Vec::with_capacity(spec.sectors.len());
        let mut next = center_cell.checked_add(1).ok_or(Error::Overflow)?;
        let mut status = Ok(());
        let mut ring = 0;
        while ring < spec.sectors.len() && status.is_ok() {
            let count = spec.sectors[ring];
            let inner = spec.center_radius + ring as i32 * spec.ring_width;
            if count < 2 || count > TURN as usize / 2 {
                status = Err(Error::InvalidSize);
            } else if i64::from(inner) * i64::from(TURN / count as i32)
                < i64::from(margin) * 2 * i64::from(TURN)
            {
                status = Err(Error::InvalidGeometry);
            } else {
                ring_starts.push(next);
                match next.checked_add(count) {
                    Some(value) => next = value,
                    None => status = Err(Error::Overflow),
                }
            }
            ring += 1;
        }
        status?;
        if spec.mode == MotionMode::Spinning {
            let clearance = i64::from(margin) * 2 * i64::from(TURN);
            let center = i64::from(spec.center_radius);
            let center_minimum = (clearance + center - 1) / center;
            // A one-unit sweep shrinks the sector's common angular interval by one.
            if i64::from(TURN / spec.sectors[0] as i32) < center_minimum + 1 {
                return Err(Error::InvalidGeometry);
            }
            let mut ring = 1;
            while ring < spec.sectors.len() && status.is_ok() {
                let radius = i64::from(spec.center_radius)
                    + (ring - 1) as i64 * i64::from(spec.ring_width)
                    + i64::from(spec.ring_width / 2);
                let minimum = (clearance + radius - 1) / radius;
                let inner_width = i64::from(TURN / spec.sectors[ring - 1] as i32);
                let outer_width = i64::from(TURN / spec.sectors[ring] as i32);
                // Conservative, not a sector-count cap: after either ring moves one unit,
                // every sector still overlaps a neighbor by the required clearance.
                // Two half-width witnesses plus a one-unit boundary gap need 2*minimum+2.
                // Unequal partitions may work below this sufficient bound; we reject them.
                if inner_width < minimum * 2 + 2 || outer_width < minimum * 2 + 2 {
                    status = Err(Error::InvalidGeometry);
                }
                ring += 1;
            }
            status?;
        }
        if let MotionMode::Twisting {
            amplitude,
            max_relative,
        } = spec.mode
        {
            if !(0..=TURN / 8).contains(&amplitude) || !(0..=TURN / 4).contains(&max_relative) {
                return Err(Error::InvalidGeometry);
            }
            let mut ring = 0;
            while ring < spec.sectors.len() && status.is_ok() {
                let relative = if ring + 1 < spec.sectors.len()
                    && spec.directions[ring] != spec.directions[ring + 1]
                {
                    amplitude * 2
                } else {
                    amplitude
                };
                if relative > max_relative
                    || i64::from(outer) * i64::from(relative) * 8
                        > i64::from(spec.ring_width - margin * 2) * i64::from(TURN)
                {
                    status = Err(Error::InvalidGeometry);
                }
                ring += 1;
            }
        }
        status?;
        Ok(Self {
            spec,
            center_cell,
            ring_starts,
            transform_start,
            outer,
        })
    }

    pub fn center_cell(&self) -> usize {
        self.center_cell
    }
    pub fn ring_count(&self) -> usize {
        self.spec.sectors.len()
    }
    pub fn mode(&self) -> MotionMode {
        self.spec.mode
    }
    pub fn outer_radius(&self) -> i32 {
        self.outer
    }
    pub fn center(&self) -> Point {
        self.spec.center
    }
    pub fn transform_start(&self) -> usize {
        self.transform_start
    }
    pub fn spec(&self) -> &PolarSpec {
        &self.spec
    }

    pub fn sector(&self, ring: usize, sector: usize) -> Option<usize> {
        if ring >= self.ring_count() || sector >= self.spec.sectors[ring] {
            return None;
        }
        Some(self.ring_starts[ring] + sector)
    }

    pub fn sector_arc(&self, ring: usize, sector: usize) -> Result<Arc, Error> {
        if self.sector(ring, sector).is_none() {
            return Err(Error::InvalidIndex);
        }
        Ok(self.arc(ring, sector))
    }

    pub fn ring_offset(&self, ring: usize, phases: &[i32]) -> Result<i32, Error> {
        if ring >= self.ring_count() || phases.len() < self.transform_start + self.ring_count() {
            return Err(Error::InvalidIndex);
        }
        Ok(self.offset(ring, phases))
    }

    pub(crate) fn arc(&self, ring: usize, sector: usize) -> Arc {
        let count = self.spec.sectors[ring] as i32;
        let start = sector as i32 * TURN / count;
        let end = (sector as i32 + 1) * TURN / count;
        Arc {
            start,
            length: end - start,
        }
    }

    pub(crate) fn radius(&self, ring: usize) -> i32 {
        self.spec.center_radius + ring as i32 * self.spec.ring_width + self.spec.ring_width / 2
    }

    pub(crate) fn offset(&self, ring: usize, phases: &[i32]) -> i32 {
        let phase = phases[self.transform_start + ring];
        let offset = match self.spec.mode {
            MotionMode::Spinning => normalize(phase) * self.spec.directions[ring].sign(),
            MotionMode::Twisting { amplitude, .. } => {
                let sine = point(Point { x: 0, y: 0 }, amplitude, phase).y;
                sine * self.spec.directions[ring].sign()
            }
        };
        normalize(offset)
    }

    /// Shared twisting deformation interpolates ring-center offsets and unwinds in the adapter.
    pub fn offset_at(&self, radius: i32, adapter_band: i32, phases: &[i32]) -> Result<i32, Error> {
        let high = self
            .outer
            .checked_add(adapter_band)
            .ok_or(Error::Overflow)?;
        if phases.len() < self.transform_start + self.ring_count()
            || radius < 0
            || radius > high
            || adapter_band <= 0
            || high > COORD_LIMIT
        {
            return Err(Error::InvalidGeometry);
        }
        Ok(self.offset_at_valid(radius, adapter_band, phases))
    }

    pub(crate) fn offset_at_valid(&self, radius: i32, adapter_band: i32, phases: &[i32]) -> i32 {
        let first = self.radius(0);
        if radius <= first {
            return self.offset(0, phases);
        }
        let mut ring = 0;
        while ring + 1 < self.ring_count() && radius >= self.radius(ring + 1) {
            ring += 1;
        }
        let low = self.radius(ring);
        let high = if ring + 1 < self.ring_count() {
            self.radius(ring + 1)
        } else {
            self.outer + adapter_band
        };
        if radius >= high {
            return 0;
        }
        let from = self.offset(ring, phases);
        let to = if ring + 1 < self.ring_count() {
            self.offset(ring + 1, phases)
        } else {
            0
        };
        normalize(
            from + (i64::from(angle_delta(from, to)) * i64::from(radius - low)
                / i64::from(high - low)) as i32,
        )
    }
}
