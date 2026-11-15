//! Unified scene publication, geometric admission, reservations, and lifecycle control.
// Measurements must include every obstacle; the adapter renders the exact shared integer embedding.
// Measurements stay immutable within an epoch; viewport bounds round inward and obstacles outward.
// Full-cell swept AABBs deliberately reject some curved corridors that a tighter embedding could admit.

use crate::grid::{Geometry, Grid, GridSpec, Point, Rect};
use crate::polar::{self, Arc, Circle, MotionMode, PolarSpec, PortalSpec, TURN};
use crate::shatter::{Patch, PatchId, Stage};
use crate::spanning_tree::{Tree, Workspace};
use crate::topology::{check_storage, Carrier, Edge, Error};
use crate::tree::Rng;
use crate::walker::{Crossing, Holds, LocalPose, Path, Reservation, Stamp, Walker, WalkerState};
use alloc::vec;
use alloc::vec::Vec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cell {
    Grid {
        column: usize,
        row: usize,
        bounds: Rect,
    },
    Center {
        circle: usize,
    },
    Sector {
        circle: usize,
        ring: usize,
        sector: usize,
    },
    Transition {
        portal: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Portal {
    pub spec: PortalSpec,
    pub grid_cell: usize,
    pub transition_cell: usize,
}

#[derive(Debug)]
pub struct Layout {
    grid: Grid,
    cells: Vec<Cell>,
    circles: Vec<Circle>,
    portals: Vec<Portal>,
    bands: Vec<i32>,
    geometry: Geometry,
    carrier: Carrier,
    transforms: usize,
}

#[derive(Debug, Clone, Copy)]
struct Doorway {
    corridor: Rect,
    path: Path,
    holds: Holds,
}

fn grid_intersects(cell: Cell, corridor: Rect, included: bool) -> bool {
    if !included {
        return false;
    }
    match cell {
        Cell::Grid { bounds, .. } => corridor.intersects(bounds),
        _ => false,
    }
}

fn disk_intersects(corridor: Rect, center: Point, radius: i32, included: bool) -> bool {
    included && corridor.touches_disk(center, radius)
}

fn oriented_path(path: Path, forward: bool) -> Path {
    if forward {
        return path;
    }
    match path {
        Path::Cartesian { from, to } => Path::Cartesian { from: to, to: from },
        Path::Polar {
            circle,
            from_radius,
            to_radius,
            from_angle,
            doorway_angle,
            to_angle,
        } => Path::Polar {
            circle,
            from_radius: to_radius,
            to_radius: from_radius,
            from_angle: to_angle,
            doorway_angle,
            to_angle: from_angle,
        },
    }
}

fn same_ring(first: Cell, second: Cell) -> bool {
    match (first, second) {
        (Cell::Sector { ring: first, .. }, Cell::Sector { ring: second, .. }) => first == second,
        _ => false,
    }
}

fn check_hold_capacity(holds: Holds, counts: &[usize]) -> Result<(), Error> {
    let mut overflow = false;
    let mut i = 0;
    while i < holds.count && !overflow {
        overflow = counts[holds.ids[i]] == usize::MAX;
        i += 1;
    }
    if overflow {
        Err(Error::Overflow)
    } else {
        Ok(())
    }
}

fn acquire_holds(counts: &mut [usize], holds: Holds) {
    let mut i = 0;
    while i < holds.count {
        counts[holds.ids[i]] += 1;
        i += 1;
    }
}

fn route_cell_status(
    interior: bool,
    result: Result<bool, Error>,
    first: bool,
    edge: Edge,
) -> (bool, Result<Option<Edge>, Error>) {
    match result {
        Ok(cell_interior) => {
            let edge = if first { None } else { Some(edge) };
            (interior || cell_interior, Ok(edge))
        }
        Err(error) => (interior, Err(error)),
    }
}

fn push_edge(edges: &mut Vec<Edge>, u: usize, v: usize) {
    edges.push(Edge::new(u, v));
}

fn contains(edges: &[Edge], edge: Edge) -> bool {
    let mut found = false;
    let mut i = 0;
    while i < edges.len() && !found {
        found = Edge::new(edges[i].u, edges[i].v) == edge;
        i += 1;
    }
    found
}

fn check_portal_spec(portal: PortalSpec, circles: &[Circle], margin: i32) -> Result<(), Error> {
    if portal.circle >= circles.len() || portal.band < margin * 4 {
        return Err(Error::InvalidGeometry);
    }
    portal.mouth.validate()?;
    if portal.mouth.length > TURN / 2 {
        return Err(Error::InvalidGeometry);
    }
    let outer = circles[portal.circle].outer;
    if i64::from(outer) * i64::from(portal.mouth.length) < i64::from(margin) * 2 * i64::from(TURN) {
        return Err(Error::InvalidGeometry);
    }
    Ok(())
}

fn check_circle_extent(
    index: usize,
    circles: &[Circle],
    bands: &[i32],
    counts: &[usize],
    margin: i32,
) -> Result<(), Error> {
    if counts[index] < 2 {
        return Err(Error::InvalidGeometry);
    }
    let circle = &circles[index];
    let radius = circle
        .outer
        .checked_add(bands[index])
        .ok_or(Error::Overflow)?;
    if radius > crate::grid::COORD_LIMIT {
        return Err(Error::InvalidGeometry);
    }
    polar::bounds(
        circle.center(),
        0,
        radius,
        Arc {
            start: 0,
            length: TURN,
        },
        margin,
    )?;
    if let MotionMode::Twisting { amplitude, .. } = circle.mode() {
        let width = circle.spec.ring_width / 2 + bands[index];
        if i64::from(radius) * i64::from(amplitude) * 8
            > i64::from(width - margin * 2) * i64::from(TURN)
        {
            return Err(Error::InvalidGeometry);
        }
    }
    let mut overlap = false;
    let mut j = 0;
    while j < index && !overlap {
        let other = circles[j].outer + bands[j];
        let distance = i64::from(radius) + i64::from(other) + i64::from(margin) * 2;
        let dx = i64::from(circle.center().x) - i64::from(circles[j].center().x);
        let dy = i64::from(circle.center().y) - i64::from(circles[j].center().y);
        overlap = dx * dx + dy * dy <= distance * distance;
        j += 1;
    }
    if overlap {
        Err(Error::InvalidGeometry)
    } else {
        Ok(())
    }
}

fn resolve_portal(
    spec: PortalSpec,
    grid: &Grid,
    portals: &[Portal],
    transition_cell: usize,
) -> Result<Portal, Error> {
    let grid_cell = grid
        .cell(spec.column, spec.row)
        .ok_or(Error::InvalidGeometry)?;
    let mut conflict = false;
    let mut j = 0;
    while j < portals.len() && !conflict {
        let previous = portals[j];
        conflict = previous.spec.circle == spec.circle
            && (previous.grid_cell == grid_cell
                || polar::overlap(
                    [
                        previous.spec.mouth,
                        spec.mouth,
                        previous.spec.mouth,
                        spec.mouth,
                    ],
                    1,
                )
                .is_ok());
        j += 1;
    }
    if conflict {
        return Err(Error::InvalidGeometry);
    }
    Ok(Portal {
        spec,
        grid_cell,
        transition_cell,
    })
}

impl Layout {
    /// Removes replaced and obstructed grid cells before assigning dense navigable IDs.
    pub fn new(
        grid_spec: GridSpec,
        specs: Vec<PolarSpec>,
        portal_specs: &[PortalSpec],
        geometry: Geometry,
    ) -> Result<Self, Error> {
        geometry.validate()?;
        let margin = geometry.margin()?;
        if grid_spec.cell_size < margin * 2 {
            return Err(Error::InvalidGeometry);
        }
        let mut grid = Grid::new(grid_spec)?;
        check_storage(specs.len(), const { core::mem::size_of::<Circle>() })?;
        check_storage(portal_specs.len(), const { core::mem::size_of::<Portal>() })?;
        let mut circles = Vec::with_capacity(specs.len());
        let mut transforms = 0usize;
        let mut status = Ok(());
        for spec in specs {
            if status.is_ok() {
                match Circle::new(spec, 0, transforms, margin) {
                    Ok(circle) => match transforms.checked_add(circle.ring_count()) {
                        Some(count) => {
                            transforms = count;
                            circles.push(circle);
                        }
                        None => status = Err(Error::Overflow),
                    },
                    Err(error) => status = Err(error),
                }
            }
        }
        status?;
        let mut bands = vec![0; circles.len()];
        let mut portal_counts = vec![0usize; circles.len()];
        let mut i = 0;
        while i < portal_specs.len() && status.is_ok() {
            let portal = portal_specs[i];
            status = check_portal_spec(portal, &circles, margin);
            if status.is_ok() {
                bands[portal.circle] = bands[portal.circle].max(portal.band);
                portal_counts[portal.circle] += 1;
            }
            i += 1;
        }
        status?;
        let mut i = 0;
        while i < circles.len() && status.is_ok() {
            status = check_circle_extent(i, &circles, &bands, &portal_counts, margin);
            i += 1;
        }
        status?;
        let mut cells = Vec::new();
        let mut row = 0;
        while row < grid_spec.rows {
            let mut column = 0;
            while column < grid_spec.columns {
                let bounds = grid.bounds(column, row);
                let mut removed = !geometry.check(bounds).is_ok();
                let mut i = 0;
                while i < circles.len() {
                    if bounds.touches_disk(circles[i].center(), circles[i].outer + bands[i]) {
                        removed = true;
                    }
                    i += 1;
                }
                if !removed {
                    grid.retain(column, row, cells.len());
                    cells.push(Cell::Grid {
                        column,
                        row,
                        bounds,
                    });
                }
                column += 1;
            }
            row += 1;
        }
        let mut ci = 0;
        while ci < circles.len() {
            let start = cells.len();
            circles[ci].center_cell = start;
            cells.push(Cell::Center { circle: ci });
            let mut ring = 0;
            while ring < circles[ci].ring_count() {
                circles[ci].ring_starts[ring] = cells.len();
                let mut sector = 0;
                while sector < circles[ci].spec.sectors[ring] {
                    cells.push(Cell::Sector {
                        circle: ci,
                        ring,
                        sector,
                    });
                    sector += 1;
                }
                ring += 1;
            }
            ci += 1;
        }
        let mut portals = Vec::with_capacity(portal_specs.len());
        let mut i = 0;
        while i < portal_specs.len() && status.is_ok() {
            match resolve_portal(portal_specs[i], &grid, &portals, cells.len()) {
                Ok(portal) => {
                    cells.push(Cell::Transition { portal: i });
                    portals.push(portal);
                }
                Err(error) => status = Err(error),
            }
            i += 1;
        }
        status?;
        if cells.is_empty() {
            return Err(Error::InvalidSize);
        }
        cells
            .len()
            .checked_mul(cells.len())
            .ok_or(Error::Overflow)?;
        let mut edges = Vec::new();
        let mut cell = 0;
        while cell < cells.len() {
            if let Cell::Grid { column, row, .. } = cells[cell] {
                if let Some(right) = grid.cell(column + 1, row) {
                    push_edge(&mut edges, cell, right);
                }
                if let Some(down) = grid.cell(column, row + 1) {
                    push_edge(&mut edges, cell, down);
                }
            }
            cell += 1;
        }
        let mut ci = 0;
        while ci < circles.len() {
            let ring_count = circles[ci].ring_count();
            let center_cell = circles[ci].center_cell;
            let mut ring = 0;
            while ring < ring_count {
                let sectors = circles[ci].spec.sectors[ring];
                let ring_start = circles[ci].ring_starts[ring];
                let mut sector = 0;
                while sector < sectors {
                    let here = ring_start + sector;
                    let next = ring_start + (sector + 1) % sectors;
                    if sectors > 2 || sector == 0 {
                        push_edge(&mut edges, here, next);
                    }
                    if ring == 0 {
                        push_edge(&mut edges, here, center_cell);
                    } else {
                        let inner_sectors = circles[ci].spec.sectors[ring - 1];
                        let inner_start = circles[ci].ring_starts[ring - 1];
                        let mut inner = 0;
                        while inner < inner_sectors {
                            push_edge(&mut edges, here, inner_start + inner);
                            inner += 1;
                        }
                    }
                    sector += 1;
                }
                ring += 1;
            }
            ci += 1;
        }
        let mut i = 0;
        while i < portals.len() {
            let portal = portals[i];
            let circle = &circles[portal.spec.circle];
            push_edge(&mut edges, portal.grid_cell, portal.transition_cell);
            let ring = circle.ring_count() - 1;
            let mut sector = 0;
            while sector < circle.spec.sectors[ring] {
                push_edge(
                    &mut edges,
                    portal.transition_cell,
                    circle.ring_starts[ring] + sector,
                );
                sector += 1;
            }
            i += 1;
        }
        let carrier = Carrier::from_edges(cells.len(), &edges)?;
        let layout = Self {
            grid,
            cells,
            circles,
            portals,
            bands,
            geometry,
            carrier,
            transforms,
        };
        let zero = vec![0; transforms];
        let mut i = 0;
        while i < layout.portals.len() && status.is_ok() {
            status = layout.check_connector(i, &zero);
            i += 1;
        }
        status?;
        Ok(layout)
    }

    fn check_connector(&self, index: usize, phases: &[i32]) -> Result<(), Error> {
        let portal = self.portals[index];
        let corridor = self
            .doorway(
                Edge::new(portal.grid_cell, portal.transition_cell),
                phases,
                phases,
            )?
            .corridor;
        let circle = &self.circles[portal.spec.circle];
        let margin = self.geometry.margin()?;
        if corridor.touches_disk(circle.center(), circle.outer + margin) {
            return Err(Error::InvalidGeometry);
        }
        let mut blocked = false;
        let mut cell = 0;
        while cell < self.cells.len() && !blocked {
            let kind = self.cells[cell];
            blocked = grid_intersects(kind, corridor, cell != portal.grid_cell);
            cell += 1;
        }
        let mut other = 0;
        while other < self.circles.len() && !blocked {
            let center = self.circles[other].center();
            let radius = self.circles[other].outer + self.bands[other] + margin;
            blocked = disk_intersects(corridor, center, radius, other != portal.spec.circle);
            other += 1;
        }
        if blocked {
            return Err(Error::InvalidGeometry);
        }
        let mut status = Ok(());
        let mut other = 0;
        while other < index && status.is_ok() {
            status = self.check_connector_pair(portal, corridor, self.portals[other], phases);
            other += 1;
        }
        status
    }

    fn check_connector_pair(
        &self,
        portal: Portal,
        corridor: Rect,
        other: Portal,
        phases: &[i32],
    ) -> Result<(), Error> {
        let other_bounds = self
            .doorway(
                Edge::new(other.grid_cell, other.transition_cell),
                phases,
                phases,
            )?
            .corridor;
        if !corridor.intersects(other_bounds) {
            return Ok(());
        }
        let intersection = Rect {
            min: Point {
                x: corridor.min.x.max(other_bounds.min.x),
                y: corridor.min.y.max(other_bounds.min.y),
            },
            max: Point {
                x: corridor.max.x.min(other_bounds.max.x),
                y: corridor.max.y.min(other_bounds.max.y),
            },
        };
        if portal.grid_cell == other.grid_cell {
            if let Cell::Grid { bounds, .. } = self.cells[portal.grid_cell] {
                if bounds.contains(intersection) {
                    return Ok(());
                }
            }
        }
        Err(Error::InvalidGeometry)
    }

    pub fn grid(&self) -> &Grid {
        &self.grid
    }
    pub fn cells(&self) -> &[Cell] {
        &self.cells
    }
    pub fn circles(&self) -> &[Circle] {
        &self.circles
    }
    pub fn portals(&self) -> &[Portal] {
        &self.portals
    }
    pub fn carrier(&self) -> &Carrier {
        &self.carrier
    }
    pub fn transform_count(&self) -> usize {
        self.transforms
    }
    pub fn geometry(&self) -> &Geometry {
        &self.geometry
    }
    /// All portals of a circle share the largest requested band and the same radial deformation.
    pub fn adapter_band(&self, circle: usize) -> Option<i32> {
        if circle < self.bands.len() {
            Some(self.bands[circle])
        } else {
            None
        }
    }

    fn circle_of(&self, cell: usize) -> Option<usize> {
        match self.cells[cell] {
            Cell::Grid { .. } => None,
            Cell::Center { circle } | Cell::Sector { circle, .. } => Some(circle),
            Cell::Transition { portal } => Some(self.portals[portal].spec.circle),
        }
    }

    fn local_pose(&self, cell: usize) -> LocalPose {
        match self.cells[cell] {
            Cell::Grid { bounds, .. } => LocalPose::Cartesian(bounds.center()),
            Cell::Center { circle } => LocalPose::Polar {
                circle,
                radius: 0,
                angle: 0,
            },
            Cell::Sector {
                circle,
                ring,
                sector,
            } => LocalPose::Polar {
                circle,
                radius: self.circles[circle].radius(ring),
                angle: self.circles[circle].arc(ring, sector).middle(),
            },
            Cell::Transition { portal } => {
                let portal = self.portals[portal];
                let circle = portal.spec.circle;
                LocalPose::Polar {
                    circle,
                    radius: self.circles[circle].outer + self.bands[circle],
                    angle: portal.spec.mouth.middle(),
                }
            }
        }
    }

    fn cell_arc(&self, cell: usize, phases: &[i32]) -> Arc {
        match self.cells[cell] {
            Cell::Sector {
                circle,
                ring,
                sector,
            } => {
                let c = &self.circles[circle];
                let arc = c.arc(ring, sector);
                match c.mode() {
                    MotionMode::Spinning => arc.shifted(c.offset(ring, phases)),
                    MotionMode::Twisting { .. } => arc,
                }
            }
            Cell::Transition { portal } => self.portals[portal].spec.mouth,
            _ => Arc {
                start: 0,
                length: TURN,
            },
        }
    }

    fn swept_arc(&self, cell: usize, arc: Arc, mode: MotionMode, next: &[i32]) -> Arc {
        match mode {
            MotionMode::Spinning => arc.swept(polar::angle_delta(
                arc.start,
                self.cell_arc(cell, next).start,
            )),
            MotionMode::Twisting { amplitude, .. } => arc.shifted(-amplitude).swept(amplitude * 2),
        }
    }

    fn frame_pose(&self, cell: usize, phases: &[i32]) -> LocalPose {
        let local = self.local_pose(cell);
        if let Cell::Sector { circle, ring, .. } = self.cells[cell] {
            if let (MotionMode::Spinning, LocalPose::Polar { radius, angle, .. }) =
                (self.circles[circle].mode(), local)
            {
                return LocalPose::Polar {
                    circle,
                    radius,
                    angle: polar::normalize(angle + self.circles[circle].offset(ring, phases)),
                };
            }
        }
        local
    }

    fn world(&self, pose: LocalPose, phases: &[i32]) -> Point {
        match pose {
            LocalPose::Cartesian(point) => point,
            LocalPose::Polar {
                circle,
                radius,
                angle,
            } => {
                let c = &self.circles[circle];
                let offset = match c.mode() {
                    MotionMode::Spinning => 0,
                    MotionMode::Twisting { .. } => {
                        c.offset_at_valid(radius, self.bands[circle], phases)
                    }
                };
                polar::point(c.center(), radius, angle + offset)
            }
        }
    }

    fn holds(&self, cell: usize, result: &mut Holds) -> Result<(), Error> {
        let Some(circle) = self.circle_of(cell) else {
            return Ok(());
        };
        let c = &self.circles[circle];
        let (first, last) = match self.cells[cell] {
            Cell::Sector { ring, .. } => match c.mode() {
                MotionMode::Spinning => (ring, ring),
                MotionMode::Twisting { .. } => {
                    (ring.saturating_sub(1), (ring + 1).min(c.ring_count() - 1))
                }
            },
            Cell::Center { .. } => match c.mode() {
                MotionMode::Spinning => return Ok(()),
                MotionMode::Twisting { .. } => (0, 0),
            },
            Cell::Transition { .. } => (c.ring_count() - 1, c.ring_count() - 1),
            Cell::Grid { .. } => return Ok(()),
        };
        let mut status = Ok(());
        let mut ring = first;
        while ring <= last && status.is_ok() {
            let id = c.transform_start + ring;
            status = result.insert(id);
            ring += 1;
        }
        status
    }

    fn cell_sweep(&self, cell: usize, phases: &[i32], next: &[i32]) -> Result<Rect, Error> {
        let margin = self.geometry.margin()?;
        match self.cells[cell] {
            Cell::Grid { bounds, .. } => Ok(bounds),
            _ => {
                let circle = self.circle_of(cell).ok_or(Error::InvalidGeometry)?;
                let center = self.circles[circle].center();
                let mode = self.circles[circle].mode();
                let center_radius = self.circles[circle].spec.center_radius;
                let ring_width = self.circles[circle].spec.ring_width;
                let circle_outer = self.circles[circle].outer;
                let (inner, outer) = match self.cells[cell] {
                    Cell::Sector { ring, .. } => {
                        let inner = center_radius + ring as i32 * ring_width;
                        (inner, inner + ring_width)
                    }
                    Cell::Center { .. } => (0, center_radius),
                    Cell::Transition { .. } => (circle_outer, circle_outer + self.bands[circle]),
                    _ => return Err(Error::InvalidGeometry),
                };
                let arc = self.cell_arc(cell, phases);
                let swept = self.swept_arc(cell, arc, mode, next);
                polar::bounds(center, inner, outer, swept, margin)
            }
        }
    }

    fn doorway(&self, edge: Edge, phases: &[i32], next: &[i32]) -> Result<Doorway, Error> {
        if edge.u >= self.cells.len()
            || edge.v >= self.cells.len()
            || !self.carrier.contains_edge(edge)
        {
            return Err(Error::InvalidIndex);
        }
        let margin = self.geometry.margin()?;
        let mut holds = Holds::new();
        self.holds(edge.u, &mut holds)?;
        self.holds(edge.v, &mut holds)?;
        let from = self.frame_pose(edge.u, phases);
        let to = self.frame_pose(edge.v, phases);
        let doorway = match (from, to) {
            (
                LocalPose::Polar {
                    circle,
                    radius: from_radius,
                    angle: from_angle,
                },
                LocalPose::Polar {
                    circle: other,
                    radius: to_radius,
                    angle: to_angle,
                },
            ) => {
                if circle != other {
                    return Err(Error::InvalidGeometry);
                }
                let center_radius = self.circles[circle].spec.center_radius;
                let a = self.cell_arc(edge.u, phases);
                let b = self.cell_arc(edge.v, phases);
                let a_next = self.cell_arc(edge.u, next);
                let b_next = self.cell_arc(edge.v, next);
                let same_ring = same_ring(self.cells[edge.u], self.cells[edge.v]);
                let angle = if same_ring {
                    if a.contains(b.start) {
                        b.start
                    } else {
                        a.start
                    }
                } else {
                    let radius = from_radius.min(to_radius).max(center_radius);
                    let minimum = ((i64::from(margin) * 2 * i64::from(TURN) + i64::from(radius)
                        - 1)
                        / i64::from(radius)) as i32;
                    polar::overlap([a, b, a_next, b_next], minimum)?.middle()
                };
                let from_angle = if from_radius == 0 { angle } else { from_angle };
                let to_angle = if to_radius == 0 { angle } else { to_angle };
                let corridor = self
                    .cell_sweep(edge.u, phases, next)?
                    .union(self.cell_sweep(edge.v, phases, next)?);
                Doorway {
                    corridor,
                    holds,
                    path: Path::Polar {
                        circle,
                        from_radius,
                        to_radius,
                        from_angle,
                        doorway_angle: angle,
                        to_angle,
                    },
                }
            }
            _ => {
                let from = self.world(from, phases);
                let to = self.world(to, phases);
                Doorway {
                    corridor: Rect::between(from, to, margin)?,
                    holds,
                    path: Path::Cartesian { from, to },
                }
            }
        };
        self.geometry.check(doorway.corridor)?;
        Ok(doorway)
    }
    fn check_spinning_portals(
        &self,
        routes: &[Route],
        phases: &mut [i32],
        next: &mut [i32],
    ) -> Result<(), Error> {
        let mut status = Ok(());
        let mut r = 0;
        while r < routes.len() && status.is_ok() {
            let circle = routes[r].circle;
            let mode = self.circles[circle].mode();
            if mode == MotionMode::Spinning {
                let ring = self.circles[circle].ring_count() - 1;
                let transform = self.circles[circle].transform_start + ring;
                let start = self.circles[circle].ring_starts[ring];
                let count = self.circles[circle].spec.sectors[ring];
                let entrance = routes[r].cells[1];
                let exit = routes[r].cells[routes[r].cells.len() - 2];
                let mut phase = 0;
                while phase < TURN && status.is_ok() {
                    phases[transform] = phase;
                    next[transform] = polar::normalize(phase + 1);
                    let mut entrance_neighbor = None;
                    let mut exit_neighbor = None;
                    let mut matched = false;
                    let mut sector = 0;
                    while sector < count && !matched {
                        let cell = start + sector;
                        let admits_entrance = self
                            .doorway(Edge::new(entrance, cell), phases, next)
                            .is_ok();
                        let admits_exit = self.doorway(Edge::new(exit, cell), phases, next).is_ok();
                        if admits_entrance {
                            if let Some(other) = exit_neighbor {
                                matched = other != cell;
                            }
                            if entrance_neighbor.is_none() {
                                entrance_neighbor = Some(cell);
                            }
                        }
                        if admits_exit {
                            if let Some(other) = entrance_neighbor {
                                matched = matched || other != cell;
                            }
                            if exit_neighbor.is_none() {
                                exit_neighbor = Some(cell);
                            }
                        }
                        sector += 1;
                    }
                    if !matched {
                        status = Err(Error::InvalidGeometry);
                    }
                    phase += 1;
                }
                phases[transform] = 0;
                next[transform] = 0;
            }
            r += 1;
        }
        status
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Route {
    pub circle: usize,
    pub cells: Vec<usize>,
}

#[derive(Copy)]
pub struct Edit<'a> {
    pub remove: &'a [Edge],
    pub add: &'a [Edge],
    pub routes: Option<&'a [Route]>,
}

impl Clone for Edit<'_> {
    fn clone(&self) -> Self {
        *self
    }
}

impl Default for Edit<'_> {
    fn default() -> Self {
        Self {
            remove: &[],
            add: &[],
            routes: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MotionEvent {
    pub stamp: Stamp,
    pub replaced: usize,
    pub moving_doorways: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Retired {
    pub epoch: u64,
    pub terminated_walkers: usize,
    pub released_reservations: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingEpoch {
    None,
    Some(u64),
}

impl PendingEpoch {
    fn is_some(self) -> bool {
        matches!(self, Self::Some(_))
    }
}

#[derive(Debug)]
pub struct Scene {
    layout: Layout,
    tree: Tree,
    work: Workspace,
    routes: Vec<Route>,
    required: Vec<Edge>,
    phases: Vec<i32>,
    next_phases: Vec<i32>,
    holds: Vec<usize>,
    walkers: Vec<Walker>,
    patches: Vec<Patch>,
    stamp: Stamp,
    clock: u64,
    wall: u64,
    reanchor: bool,
    suspended: bool,
    inactive: bool,
    latest_request: u64,
    pending: PendingEpoch,
    trail_revision: u64,
}

#[derive(Copy)]
struct RoutePublication<'tree, 'remove, 'add> {
    tree: Option<&'tree Tree>,
    remove: &'remove [Edge],
    add: &'add [Edge],
}

impl Clone for RoutePublication<'_, '_, '_> {
    fn clone(&self) -> Self {
        *self
    }
}

fn check_routes(
    layout: &Layout,
    routes: &[Route],
    phases: &[i32],
    next: &[i32],
    tree: Option<&Tree>,
    edit: Edit<'_>,
    required: &mut Vec<Edge>,
) -> Result<(), Error> {
    if routes.len() != layout.circles.len() {
        return Err(Error::InvalidGeometry);
    }
    required.resize(0, Edge::new(0, 0));
    let publication = RoutePublication {
        tree,
        remove: edit.remove,
        add: edit.add,
    };
    let mut status = Ok(());
    let mut r = 0;
    while r < routes.len() && status.is_ok() {
        status = check_route(layout, &routes[r], r, phases, next, publication, required);
        r += 1;
    }
    status
}

fn check_route(
    layout: &Layout,
    route: &Route,
    circle: usize,
    phases: &[i32],
    next: &[i32],
    publication: RoutePublication<'_, '_, '_>,
    required: &mut Vec<Edge>,
) -> Result<(), Error> {
    if route.circle != circle || route.cells.len() < 7 || route.cells.len() > layout.cells.len() {
        return Err(Error::InvalidGeometry);
    }
    let mut status = Ok(());
    let mut interior = false;
    let mut previous = 0;
    let mut i = 0;
    while i < route.cells.len() && status.is_ok() {
        let cell = route.cells[i];
        let checked = route_cell_status(
            interior,
            check_route_cell(layout, route, i),
            i == 0,
            Edge::new(previous, cell),
        );
        interior = checked.0;
        status = check_route_edge(layout, checked.1, phases, next, publication, required);
        previous = cell;
        i += 1;
    }
    status?;
    if interior {
        Ok(())
    } else {
        Err(Error::InvalidGeometry)
    }
}

fn check_route_cell(layout: &Layout, route: &Route, i: usize) -> Result<bool, Error> {
    let cell = route.cells[i];
    if cell >= layout.cells.len() {
        return Err(Error::InvalidIndex);
    }
    let mut duplicate = false;
    let mut j = 0;
    while j < i && !duplicate {
        duplicate = route.cells[j] == cell;
        j += 1;
    }
    if duplicate {
        return Err(Error::InvalidForest);
    }
    let last = route.cells.len() - 1;
    let mut interior = false;
    let cell = layout.cells[cell];
    match cell {
        Cell::Grid { .. } if i == 0 || i == last => {}
        Cell::Transition { portal } if i == 1 || i == last - 1 => {
            let portal = layout.portals[portal];
            let exterior_index = if i == 1 { 0 } else { last };
            let exterior = route.cells[exterior_index];
            if portal.spec.circle != route.circle || portal.grid_cell != exterior {
                return Err(Error::InvalidGeometry);
            }
        }
        Cell::Center { circle } if i > 1 && i < last - 1 && circle == route.circle => {
            interior = true
        }
        Cell::Sector { circle, ring, .. } if i > 1 && i < last - 1 && circle == route.circle => {
            if ring + 1 < layout.circles[circle].ring_count() {
                interior = true;
            }
        }
        _ => return Err(Error::InvalidGeometry),
    }
    Ok(interior)
}

fn check_route_edge(
    layout: &Layout,
    edge: Result<Option<Edge>, Error>,
    phases: &[i32],
    next: &[i32],
    publication: RoutePublication<'_, '_, '_>,
    required: &mut Vec<Edge>,
) -> Result<(), Error> {
    let edge = match edge? {
        Some(edge) => edge,
        None => return Ok(()),
    };
    layout.doorway(edge, phases, next)?;
    if let Some(tree) = publication.tree {
        if !contains(publication.add, edge)
            && (!tree.has_edge(edge) || contains(publication.remove, edge))
        {
            return Err(Error::InvalidTransition);
        }
    }
    if !required.contains(&edge) {
        // Scene reserves this carrier-edge budget once and never shrinks the workspace.
        if required.len() == layout.carrier.edges().len() {
            return Err(Error::InsufficientWorkspace);
        }
        required.push(edge);
    }
    Ok(())
}

impl Scene {
    pub fn new<R: Rng>(
        layout: Layout,
        routes: &[Route],
        occupants: &[usize],
        patch_capacity: usize,
        epoch: u64,
        rng: &mut R,
    ) -> Result<Self, Error> {
        let count = layout.cells.len();
        let patch_cells = patch_capacity.checked_mul(count).ok_or(Error::Overflow)?;
        let route_cells = routes.len().checked_mul(count).ok_or(Error::Overflow)?;
        check_storage(patch_cells, const { core::mem::size_of::<bool>() })?;
        check_storage(route_cells, const { core::mem::size_of::<usize>() })?;
        check_storage(patch_capacity, const { core::mem::size_of::<Patch>() })?;
        check_storage(occupants.len(), const { core::mem::size_of::<Walker>() })?;
        check_storage(routes.len(), const { core::mem::size_of::<Route>() })?;
        check_storage(layout.transforms, const { core::mem::size_of::<usize>() })?;
        let mut phases = vec![0; layout.transforms];
        let mut next_phases = vec![0; layout.transforms];
        let mut required = Vec::with_capacity(layout.carrier.edges().len());
        check_routes(
            &layout,
            routes,
            &phases,
            &phases,
            None,
            Edit::default(),
            &mut required,
        )?;
        // Exact chosen-pair two-matching over every quantized one-unit outer-ring sweep.
        // Neighbor sets may overlap: only the two selected neighbors must be distinct.
        layout.check_spinning_portals(routes, &mut phases, &mut next_phases)?;
        let mut live_edges = Vec::with_capacity(layout.carrier.edges().len());
        let mut i = 0;
        while i < layout.carrier.edges().len() {
            let edge = layout.carrier.edges()[i];
            if layout.doorway(edge, &phases, &phases).is_ok() {
                live_edges.push(edge);
            }
            i += 1;
        }
        let live = Carrier::from_edges(count, &live_edges)?;
        let mut work = Workspace::new(count, layout.carrier.edges().len())?;
        let tree = Tree::scene_dfs(&live, &required, 0, rng, &mut work)?;
        let mut saved_routes = Vec::with_capacity(routes.len());
        let mut i = 0;
        while i < routes.len() {
            let mut cells = Vec::with_capacity(count);
            cells.extend_from_slice(&routes[i].cells);
            saved_routes.push(Route {
                circle: routes[i].circle,
                cells,
            });
            i += 1;
        }
        let mut walkers = Vec::with_capacity(occupants.len());
        let mut valid = true;
        let mut i = 0;
        while i < occupants.len() && valid {
            let cell = occupants[i];
            valid = cell < count;
            if valid {
                walkers.push(Walker {
                    cell,
                    local: layout.local_pose(cell),
                    state: WalkerState::Ready,
                });
            }
            i += 1;
        }
        if !valid {
            return Err(Error::InvalidIndex);
        }
        let mut patches = Vec::with_capacity(patch_capacity);
        let mut i = 0;
        while i < patch_capacity {
            patches.push(Patch::new(count));
            i += 1;
        }
        Ok(Self {
            next_phases,
            holds: vec![0; layout.transforms],
            layout,
            tree,
            work,
            routes: saved_routes,
            required,
            phases,
            walkers,
            patches,
            stamp: Stamp { epoch, revision: 0 },
            clock: 0,
            wall: 0,
            reanchor: false,
            suspended: false,
            inactive: false,
            latest_request: epoch,
            pending: PendingEpoch::None,
            trail_revision: 0,
        })
    }

    pub fn stamp(&self) -> Stamp {
        self.stamp
    }
    pub fn layout(&self) -> &Layout {
        &self.layout
    }
    pub fn tree(&self) -> &Tree {
        &self.tree
    }
    pub fn routes(&self) -> &[Route] {
        &self.routes
    }
    pub fn phases(&self) -> &[i32] {
        &self.phases
    }
    pub fn holds(&self) -> &[usize] {
        &self.holds
    }
    pub fn walkers(&self) -> &[Walker] {
        &self.walkers
    }
    pub fn clock(&self) -> u64 {
        self.clock
    }
    /// Renderers discard historical trails whenever this revision changes.
    pub fn trail_revision(&self) -> u64 {
        self.trail_revision
    }
    pub fn is_suspended(&self) -> bool {
        self.suspended
    }
    pub fn is_inactive(&self) -> bool {
        self.inactive
    }

    fn check_stamp(&self, stamp: Stamp) -> Result<u64, Error> {
        if stamp.epoch != self.stamp.epoch {
            return Err(Error::StaleEpoch);
        }
        if stamp.revision != self.stamp.revision {
            return Err(Error::StaleRevision);
        }
        self.stamp.revision.checked_add(1).ok_or(Error::Overflow)
    }

    fn admission(&self, cell: usize) -> Result<(), Error> {
        if cell >= self.layout.cells.len() {
            return Err(Error::InvalidIndex);
        }
        if self.suspended || self.inactive || self.pending.is_some() {
            return Err(Error::InvalidTransition);
        }
        let mut occupied = false;
        let mut i = 0;
        while i < self.patches.len() && !occupied {
            occupied = self.patches[i].contains(cell);
            i += 1;
        }
        if occupied {
            Err(Error::Occupied)
        } else {
            Ok(())
        }
    }

    pub fn cell_pose(&self, cell: usize) -> Result<Point, Error> {
        if cell >= self.layout.cells.len() {
            return Err(Error::InvalidIndex);
        }
        Ok(self
            .layout
            .world(self.layout.frame_pose(cell, &self.phases), &self.phases))
    }

    pub fn walker_pose(&self, walker: usize) -> Result<Point, Error> {
        let walker = self.walkers.get(walker).ok_or(Error::InvalidIndex)?;
        match walker.state {
            WalkerState::Terminated => Err(Error::InvalidTransition),
            WalkerState::Crossing(crossing) => Ok(self.layout.world(
                crossing.path.pose(crossing.elapsed, crossing.duration),
                &self.phases,
            )),
            _ => self.cell_pose(walker.cell),
        }
    }

    pub fn doorway_bounds(&self, edge: Edge) -> Result<Rect, Error> {
        Ok(self
            .layout
            .doorway(edge, &self.phases, &self.phases)?
            .corridor)
    }

    /// Allows an event planner to inspect candidate edges without changing published state.
    pub fn swept_doorway(&mut self, edge: Edge, steps: &[i32]) -> Result<Rect, Error> {
        if steps.len() != self.phases.len() {
            return Err(Error::InvalidSize);
        }
        let mut status = Ok(());
        let mut i = 0;
        while i < steps.len() && status.is_ok() {
            if steps[i] < 0 || steps[i] > TURN / 8 {
                status = Err(Error::InvalidGeometry);
            } else {
                self.next_phases[i] = polar::normalize(self.phases[i] + steps[i]);
            }
            i += 1;
        }
        status?;
        Ok(self
            .layout
            .doorway(edge, &self.phases, &self.next_phases)?
            .corridor)
    }

    /// A reservation remains valid across unrelated revisions, but never across epochs or reuse.
    pub fn reservation(&self, token: Reservation) -> Result<&Crossing, Error> {
        if token.epoch != self.stamp.epoch {
            return Err(Error::StaleEpoch);
        }
        let walker = self.walkers.get(token.walker).ok_or(Error::InvalidIndex)?;
        match &walker.state {
            WalkerState::Crossing(crossing) if crossing.reservation == token => Ok(crossing),
            _ => Err(Error::InvalidTransition),
        }
    }

    pub fn begin_crossing(
        &mut self,
        stamp: Stamp,
        walker: usize,
        target: usize,
        duration: u32,
    ) -> Result<Reservation, Error> {
        let revision = self.check_stamp(stamp)?;
        let occupant = *self.walkers.get(walker).ok_or(Error::InvalidIndex)?;
        if occupant.state != WalkerState::Ready || duration == 0 {
            return Err(Error::InvalidTransition);
        }
        self.admission(occupant.cell)?;
        self.admission(target)?;
        let edge = Edge::new(occupant.cell, target);
        if !self.tree.has_edge(edge) {
            return Err(Error::InvalidTransition);
        }
        let door = self.layout.doorway(edge, &self.phases, &self.phases)?;
        check_hold_capacity(door.holds, &self.holds)?;
        let path = oriented_path(door.path, occupant.cell == edge.u);
        let token = Reservation {
            epoch: self.stamp.epoch,
            walker,
            serial: revision,
        };
        let crossing = Crossing {
            source: occupant.cell,
            target,
            elapsed: 0,
            duration,
            reservation: token,
            corridor: door.corridor,
            path,
            target_pose: self.layout.local_pose(target),
            holds: door.holds,
        };
        acquire_holds(&mut self.holds, door.holds);
        self.walkers[walker].state = WalkerState::Crossing(crossing);
        self.stamp.revision = revision;
        Ok(token)
    }

    pub(crate) fn check_removal(&self, edge: Edge) -> Result<(), Error> {
        if !self.tree.has_edge(edge) {
            return Err(Error::InvalidTransition);
        }
        let removed = self.layout.doorway(edge, &self.phases, &self.phases)?;
        let mut occupied = false;
        let mut w = 0;
        while w < self.walkers.len() && !occupied {
            if let WalkerState::Crossing(crossing) = self.walkers[w].state {
                occupied = removed.corridor.intersects(crossing.corridor);
            }
            w += 1;
        }
        if occupied {
            Err(Error::Occupied)
        } else {
            Ok(())
        }
    }

    fn preflight_edit(&mut self, edit: Edit<'_>) -> Result<usize, Error> {
        if edit.remove.len() != edit.add.len() {
            return Err(Error::InvalidTransition);
        }
        let mut status = Ok(());
        let mut i = 0;
        while i < edit.remove.len() && status.is_ok() {
            status = self.check_removal(Edge::new(edit.remove[i].u, edit.remove[i].v));
            i += 1;
        }
        status?;
        match edit.routes {
            Some(routes) => check_routes(
                &self.layout,
                routes,
                &self.phases,
                &self.next_phases,
                Some(&self.tree),
                edit,
                &mut self.required,
            ),
            None => check_routes(
                &self.layout,
                &self.routes,
                &self.phases,
                &self.next_phases,
                Some(&self.tree),
                edit,
                &mut self.required,
            ),
        }?;
        let mut moving = 0;
        let mut cell = 0;
        while cell < self.tree.parents().len() && status.is_ok() {
            let parent = self.tree.parents()[cell];
            if parent != cell {
                let edge = Edge::new(cell, parent);
                if !contains(edit.remove, edge) {
                    if let Err(error) = self.layout.doorway(edge, &self.phases, &self.next_phases) {
                        status = Err(error);
                    }
                    if self
                        .layout
                        .world(self.layout.frame_pose(cell, &self.phases), &self.phases)
                        != self.layout.world(
                            self.layout.frame_pose(cell, &self.next_phases),
                            &self.next_phases,
                        )
                        || self
                            .layout
                            .world(self.layout.frame_pose(parent, &self.phases), &self.phases)
                            != self.layout.world(
                                self.layout.frame_pose(parent, &self.next_phases),
                                &self.next_phases,
                            )
                    {
                        moving += 1;
                    }
                }
            }
            cell += 1;
        }
        let mut i = 0;
        while i < edit.add.len() && status.is_ok() {
            if let Err(error) = self.layout.doorway(
                Edge::new(edit.add[i].u, edit.add[i].v),
                &self.phases,
                &self.next_phases,
            ) {
                status = Err(error);
            }
            i += 1;
        }
        status?;
        Ok(moving)
    }

    fn check_patch_motion(&self, cell: usize, steps: &[i32]) -> Result<(), Error> {
        let mut dependencies = Holds::new();
        self.layout.holds(cell, &mut dependencies)?;
        let mut occupied = false;
        let mut j = 0;
        while j < dependencies.count && !occupied {
            occupied = steps[dependencies.ids[j]] != 0;
            j += 1;
        }
        if occupied {
            Err(Error::Occupied)
        } else {
            Ok(())
        }
    }

    fn commit_edit(&mut self, edit: Edit<'_>, revision: u64) {
        if let Some(routes) = edit.routes {
            let mut i = 0;
            while i < routes.len() {
                self.routes[i].cells.resize(0, 0);
                self.routes[i].cells.extend_from_slice(&routes[i].cells);
                i += 1;
            }
        }
        let mut i = 0;
        while i < self.phases.len() {
            self.phases[i] = self.next_phases[i];
            i += 1;
        }
        if !edit.remove.is_empty() {
            self.trail_revision = revision;
        }
        self.stamp.revision = revision;
    }

    /// Publishes a boundary-event replacement and its whole-interval geometry together.
    /// Steps are bounded to one eighth-turn; rejected steps consume no phase time.
    pub fn motion(
        &mut self,
        stamp: Stamp,
        steps: &[i32],
        edit: Edit<'_>,
    ) -> Result<MotionEvent, Error> {
        let revision = self.prepare_motion(stamp, steps)?;
        let mut stationary = true;
        let mut i = 0;
        while i < steps.len() && stationary {
            stationary = steps[i] == 0;
            i += 1;
        }
        if stationary && edit.remove.is_empty() && edit.add.is_empty() && edit.routes.is_none() {
            self.stamp.revision = revision;
            return Ok(MotionEvent {
                stamp: self.stamp,
                replaced: 0,
                moving_doorways: 0,
            });
        }
        let moving = self.preflight_edit(edit)?;
        if !edit.remove.is_empty() {
            self.tree
                .edit_edges(&self.layout.carrier, edit.remove, edit.add, &mut self.work)?;
        }
        self.commit_edit(edit, revision);
        Ok(MotionEvent {
            stamp: self.stamp,
            replaced: edit.remove.len(),
            moving_doorways: moving,
        })
    }

    /// A carver publishes its new passage before the separate crossing admission.
    pub fn carve(
        &mut self,
        stamp: Stamp,
        walker: usize,
        target: usize,
        edit: Edit<'_>,
    ) -> Result<Stamp, Error> {
        self.check_stamp(stamp)?;
        let occupant = self.walkers.get(walker).ok_or(Error::InvalidIndex)?;
        if occupant.state != WalkerState::Ready {
            return Err(Error::Occupied);
        }
        self.admission(occupant.cell)?;
        self.admission(target)?;
        let edge = Edge::new(occupant.cell, target);
        if self.tree.has_edge(edge) || !contains(edit.add, edge) {
            return Err(Error::InvalidTransition);
        }
        let mut i = 0;
        while i < self.phases.len() {
            self.next_phases[i] = self.phases[i];
            i += 1;
        }
        self.preflight_edit(edit)?;
        let revision = self.stamp.revision + 1;
        self.tree
            .edit_edges(&self.layout.carrier, edit.remove, edit.add, &mut self.work)?;
        self.commit_edit(edit, revision);
        Ok(self.stamp)
    }

    fn drain_patches(&mut self) {
        let mut p = 0;
        while p < self.patches.len() {
            if self.patches[p].stage == Stage::Draining {
                let mut crossing = false;
                let mut w = 0;
                while w < self.walkers.len() {
                    if let WalkerState::Crossing(active) = self.walkers[w].state {
                        if self.patches[p].contains(active.source)
                            || self.patches[p].contains(active.target)
                        {
                            crossing = true;
                        }
                    }
                    w += 1;
                }
                if !crossing {
                    self.patches[p].stage = Stage::Parked;
                    let mut w = 0;
                    while w < self.walkers.len() {
                        if self.patches[p].contains(self.walkers[w].cell) {
                            self.walkers[w].state = WalkerState::Parked;
                        }
                        w += 1;
                    }
                }
            }
            p += 1;
        }
    }

    /// Wall timestamps are reanchored while frozen; suspended time never becomes simulation debt.
    pub fn tick(&mut self, stamp: Stamp, wall: u64) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        if wall < self.wall {
            return Err(Error::InvalidTransition);
        }
        if self.suspended || self.inactive || self.pending.is_some() {
            self.wall = wall;
            self.stamp.revision = revision;
            return Ok(self.stamp);
        }
        if self.reanchor {
            self.wall = wall;
            self.reanchor = false;
            self.stamp.revision = revision;
            return Ok(self.stamp);
        }
        let delta = wall - self.wall;
        let clock = self.clock.checked_add(delta).ok_or(Error::Overflow)?;
        let mut w = 0;
        while w < self.walkers.len() {
            if let WalkerState::Crossing(mut crossing) = self.walkers[w].state {
                let remaining = u64::from(crossing.duration - crossing.elapsed);
                if delta >= remaining {
                    self.walkers[w].cell = crossing.target;
                    self.walkers[w].local = crossing.target_pose;
                    self.walkers[w].state = WalkerState::Ready;
                    let mut i = 0;
                    while i < crossing.holds.count {
                        self.holds[crossing.holds.ids[i]] -= 1;
                        i += 1;
                    }
                } else {
                    crossing.elapsed += delta as u32;
                    self.walkers[w].state = WalkerState::Crossing(crossing);
                }
            }
            w += 1;
        }
        self.clock = clock;
        self.wall = wall;
        self.drain_patches();
        let mut p = 0;
        while p < self.patches.len() {
            if let Stage::Reforming { until } = self.patches[p].stage {
                if clock >= until {
                    let mut w = 0;
                    while w < self.walkers.len() {
                        if self.patches[p].contains(self.walkers[w].cell) {
                            self.walkers[w].state = WalkerState::Ready;
                        }
                        w += 1;
                    }
                    self.patches[p].stage = Stage::Idle;
                }
            }
            p += 1;
        }
        self.stamp.revision = revision;
        Ok(self.stamp)
    }

    pub fn suspend(&mut self, stamp: Stamp, wall: u64) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        if wall < self.wall {
            return Err(Error::InvalidTransition);
        }
        self.wall = wall;
        self.suspended = true;
        self.stamp.revision = revision;
        Ok(self.stamp)
    }

    pub fn resume(&mut self, stamp: Stamp, wall: u64) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        if wall < self.wall {
            return Err(Error::InvalidTransition);
        }
        self.wall = wall;
        self.suspended = false;
        self.reanchor = self.pending.is_some() || self.inactive;
        self.stamp.revision = revision;
        Ok(self.stamp)
    }

    pub fn begin_shatter(&mut self, stamp: Stamp, cells: &[usize]) -> Result<PatchId, Error> {
        let revision = self.check_stamp(stamp)?;
        if cells.is_empty() {
            return Err(Error::InvalidSize);
        }
        if self.suspended || self.inactive || self.pending.is_some() {
            return Err(Error::InvalidTransition);
        }
        let mut status = Ok(());
        let mut i = 0;
        while i < cells.len() && status.is_ok() {
            status = self.admission(cells[i]);
            let mut j = 0;
            while j < i && status.is_ok() {
                if cells[j] == cells[i] {
                    status = Err(Error::InvalidIndex);
                }
                j += 1;
            }
            i += 1;
        }
        status?;
        let mut slot = 0;
        while slot < self.patches.len() && self.patches[slot].stage != Stage::Idle {
            slot += 1;
        }
        if slot == self.patches.len() {
            return Err(Error::InsufficientWorkspace);
        }
        self.patches[slot].cells.fill(false);
        let mut i = 0;
        while i < cells.len() {
            self.patches[slot].cells[cells[i]] = true;
            i += 1;
        }
        self.patches[slot].serial = revision;
        self.patches[slot].stage = Stage::Draining;
        self.drain_patches();
        self.trail_revision = revision;
        self.stamp.revision = revision;
        Ok(PatchId {
            epoch: self.stamp.epoch,
            slot,
            serial: revision,
        })
    }

    fn patch_slot(&self, id: PatchId) -> Result<usize, Error> {
        if id.epoch != self.stamp.epoch {
            return Err(Error::StaleEpoch);
        }
        let patch = self.patches.get(id.slot).ok_or(Error::InvalidIndex)?;
        patch.validate(id)?;
        Ok(id.slot)
    }

    pub fn patch_stage(&self, id: PatchId) -> Result<Stage, Error> {
        Ok(self.patches[self.patch_slot(id)?].stage)
    }

    pub fn hide_patch(&mut self, stamp: Stamp, id: PatchId) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        let slot = self.patch_slot(id)?;
        if self.suspended || self.pending.is_some() || self.inactive {
            return Err(Error::InvalidTransition);
        }
        if self.patches[slot].stage != Stage::Parked {
            return Err(Error::Occupied);
        }
        let mut w = 0;
        while w < self.walkers.len() {
            if self.patches[slot].contains(self.walkers[w].cell) {
                self.walkers[w].state = WalkerState::Hidden;
            }
            w += 1;
        }
        self.patches[slot].stage = Stage::Hidden;
        self.stamp.revision = revision;
        Ok(self.stamp)
    }

    pub fn scatter_patch(
        &mut self,
        stamp: Stamp,
        id: PatchId,
        duration: u64,
    ) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        let slot = self.patch_slot(id)?;
        if self.suspended
            || self.pending.is_some()
            || self.inactive
            || self.patches[slot].stage != Stage::Hidden
            || duration == 0
        {
            return Err(Error::InvalidTransition);
        }
        let until = self.clock.checked_add(duration).ok_or(Error::Overflow)?;
        self.patches[slot].stage = Stage::Scattered { until };
        self.stamp.revision = revision;
        Ok(self.stamp)
    }

    /// Patch edits pass the same route and reservation checks before a shared reopen deadline.
    pub fn reform_patch(
        &mut self,
        stamp: Stamp,
        id: PatchId,
        duration: u64,
        edit: Edit<'_>,
    ) -> Result<Stamp, Error> {
        let revision = self.check_stamp(stamp)?;
        let slot = self.patch_slot(id)?;
        if self.suspended || self.pending.is_some() || self.inactive || duration == 0 {
            return Err(Error::InvalidTransition);
        }
        match self.patches[slot].stage {
            Stage::Scattered { until } if self.clock >= until => {}
            _ => return Err(Error::InvalidTransition),
        }
        let until = self.clock.checked_add(duration).ok_or(Error::Overflow)?;
        let mut outside = false;
        let mut i = 0;
        while i < edit.remove.len() && !outside {
            let edge = edit.remove[i];
            outside = !self.patches[slot].contains(edge.u) || !self.patches[slot].contains(edge.v);
            i += 1;
        }
        let mut i = 0;
        while i < edit.add.len() && !outside {
            let edge = edit.add[i];
            outside = !self.patches[slot].contains(edge.u) || !self.patches[slot].contains(edge.v);
            i += 1;
        }
        if outside {
            return Err(Error::InvalidTransition);
        }
        let mut i = 0;
        while i < self.phases.len() {
            self.next_phases[i] = self.phases[i];
            i += 1;
        }
        self.preflight_edit(edit)?;
        if !edit.remove.is_empty() {
            self.tree
                .edit_edges(&self.layout.carrier, edit.remove, edit.add, &mut self.work)?;
        }
        self.commit_edit(edit, revision);
        self.patches[slot].stage = Stage::Reforming { until };
        self.trail_revision = revision;
        Ok(self.stamp)
    }

    pub fn request_layout(&mut self, stamp: Stamp) -> Result<u64, Error> {
        let revision = self.check_stamp(stamp)?;
        let request = self.latest_request.checked_add(1).ok_or(Error::Overflow)?;
        self.latest_request = request;
        self.pending = PendingEpoch::Some(request);
        self.reanchor = true;
        self.stamp.revision = revision;
        Ok(request)
    }

    pub fn publish_layout(&mut self, request: u64, mut candidate: Self) -> Result<Retired, Error> {
        if self.pending != PendingEpoch::Some(request)
            || self.latest_request != request
            || candidate.stamp.epoch != request
        {
            return Err(Error::StaleEpoch);
        }
        if candidate.stamp.revision != 0 {
            return Err(Error::InvalidTransition);
        }
        let mut retired = Retired {
            epoch: self.stamp.epoch,
            terminated_walkers: self.walkers.len(),
            released_reservations: 0,
        };
        let mut w = 0;
        while w < self.walkers.len() {
            if let WalkerState::Crossing(_) = self.walkers[w].state {
                retired.released_reservations += 1;
            }
            self.walkers[w].state = WalkerState::Terminated;
            w += 1;
        }
        self.holds.fill(0);
        candidate.suspended = self.suspended;
        candidate.wall = self.wall;
        candidate.reanchor = true;
        candidate.latest_request = request;
        *self = candidate;
        Ok(retired)
    }

    fn cell_fits(&self, cell: usize, viewport: Rect) -> Result<bool, Error> {
        let parent = self.tree.parents()[cell];
        let bounds = if parent != cell {
            self.layout
                .doorway(Edge::new(cell, parent), &self.phases, &self.phases)?
                .corridor
        } else {
            let pose = self.cell_pose(cell)?;
            Rect::between(pose, pose, self.layout.geometry.margin()?)?
        };
        Ok(viewport.contains(bounds))
    }

    /// A rejected replacement resumes only when the old swept corridors fit the new viewport.
    pub fn reject_layout(&mut self, request: u64, viewport: Rect) -> Result<Stamp, Error> {
        if self.pending != PendingEpoch::Some(request) || self.latest_request != request {
            return Err(Error::StaleEpoch);
        }
        viewport.validate()?;
        let revision = self.stamp.revision.checked_add(1).ok_or(Error::Overflow)?;
        let mut fits = true;
        let mut status = Ok(());
        let mut cell = 0;
        while cell < self.tree.parents().len() && status.is_ok() {
            match self.cell_fits(cell, viewport) {
                Ok(inside) => fits = fits && inside,
                Err(error) => status = Err(error),
            }
            cell += 1;
        }
        status?;
        self.pending = PendingEpoch::None;
        self.inactive = !fits;
        self.stamp.revision = revision;
        Ok(self.stamp)
    }
    pub(crate) fn prepare_motion(&mut self, stamp: Stamp, steps: &[i32]) -> Result<u64, Error> {
        let revision = self.check_stamp(stamp)?;
        if self.suspended || self.inactive || self.pending.is_some() {
            return Err(Error::InvalidTransition);
        }
        if steps.len() != self.phases.len() {
            return Err(Error::InvalidSize);
        }
        let mut status = Ok(());
        let mut i = 0;
        while i < steps.len() && status.is_ok() {
            if steps[i] < 0 || steps[i] > TURN / 8 {
                status = Err(Error::InvalidGeometry);
            } else if steps[i] != 0 && self.holds[i] != 0 {
                status = Err(Error::Occupied);
            } else {
                self.next_phases[i] = polar::normalize(self.phases[i] + steps[i]);
            }
            i += 1;
        }
        status?;
        let mut ci = 0;
        while ci < self.layout.circles.len() && status.is_ok() {
            let c = &self.layout.circles[ci];
            if let MotionMode::Twisting { .. } = c.mode() {
                let mut ring = 1;
                while ring < c.ring_count() && status.is_ok() {
                    if steps[c.transform_start + ring] != steps[c.transform_start] {
                        status = Err(Error::InvalidGeometry);
                    }
                    ring += 1;
                }
            }
            ci += 1;
        }
        status?;
        let mut p = 0;
        while p < self.patches.len() && status.is_ok() {
            if self.patches[p].stage != Stage::Idle {
                let mut cell = 0;
                while cell < self.layout.cells.len() && status.is_ok() {
                    if self.patches[p].cells[cell] {
                        status = self.check_patch_motion(cell, steps);
                    }
                    cell += 1;
                }
            }
            p += 1;
        }
        status?;
        Ok(revision)
    }

    pub(crate) fn motion_edge(&self, edge: Edge) -> Result<(), Error> {
        self.layout.doorway(edge, &self.phases, &self.next_phases)?;
        Ok(())
    }

    /// Plans a sparse boundary exchange, returning the divisor of the consumed phase interval.
    /// Errors preserve published state, including when no positive safe prefix exists.
    pub fn advance_motion(
        &mut self,
        expected: Stamp,
        requested_steps: &[i32],
        work: &mut crate::motion::MotionWorkspace,
    ) -> Result<crate::motion::MotionAdvance, Error> {
        work.advance(self, expected, requested_steps)
    }
}
