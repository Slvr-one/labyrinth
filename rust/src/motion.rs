//! Allocation-free boundary planning with vertex-disjoint routes and sparse tree exchanges.

use crate::scene::{Cell, Edit, MotionEvent, Route, Scene};
use crate::topology::{check_storage, Edge, Error};
use crate::walker::Stamp;
use alloc::vec;
use alloc::vec::Vec;

/// A single publication; consumed increments are the requested increments divided by `divisor`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MotionAdvance {
    /// The one atomically published transition.
    pub event: MotionEvent,
    /// Positive integer subdivision; zero requests return one.
    pub divisor: usize,
}

/// Reusable, epoch-bound planner storage. Construct again after replacing a scene's layout.
#[derive(Debug)]
pub struct MotionWorkspace {
    epoch: u64,
    cells: usize,
    edges: usize,
    endpoints: Vec<[usize; 4]>,
    steps: Vec<i32>,
    routes: Vec<Route>,
    routes_changed: bool,
    remove: Vec<Edge>,
    add: Vec<Edge>,
    admissible: Vec<bool>,
    protected: Vec<bool>,
    locked: Vec<bool>,
    // The split-vertex residual network is built once, never rebuilt during planning.
    from: Vec<usize>,
    to: Vec<usize>,
    offsets: Vec<usize>,
    arcs: Vec<usize>,
    residual: Vec<u8>,
    parent: Vec<usize>,
    queue: Vec<usize>,
    first: Vec<usize>,
    second: Vec<usize>,
}

fn network_sizes(cells: usize, edges: usize) -> Result<(usize, usize), Error> {
    let split = cells.checked_mul(2).ok_or(Error::Overflow)?;
    let nodes = split.checked_add(1).ok_or(Error::Overflow)?;
    let pairs = cells.checked_add(edges).ok_or(Error::Overflow)?;
    let arcs = pairs.checked_mul(4).ok_or(Error::Overflow)?;
    let offsets = nodes.checked_add(1).ok_or(Error::Overflow)?;
    check_storage(arcs, const { core::mem::size_of::<usize>() })?;
    check_storage(offsets, const { core::mem::size_of::<usize>() })?;
    Ok((nodes, arcs))
}

impl MotionWorkspace {
    /// Allocates checked scratch for this scene's carrier, routes and transforms.
    ///
    /// # Errors
    /// Returns [`Error::Overflow`] when network or route capacities cannot be represented.
    pub fn new(scene: &Scene) -> Result<Self, Error> {
        let cells = scene.layout().cells().len();
        let edges = scene.layout().carrier().edges().len();
        let (nodes, arc_count) = network_sizes(cells, edges)?;
        let offset_count = nodes + 1;
        let route_cells = cells
            .checked_mul(scene.routes().len())
            .ok_or(Error::Overflow)?;
        check_storage(route_cells, const { core::mem::size_of::<usize>() })?;
        check_storage(cells, const { core::mem::size_of::<Edge>() })?;
        check_storage(
            scene.routes().len(),
            const { core::mem::size_of::<Route>() },
        )?;
        check_storage(
            scene.routes().len(),
            const { core::mem::size_of::<[usize; 4]>() },
        )?;
        check_storage(scene.phases().len(), const { core::mem::size_of::<i32>() })?;
        let mut work = Self {
            epoch: scene.stamp().epoch,
            cells,
            edges,
            endpoints: Vec::with_capacity(scene.routes().len()),
            steps: vec![0; scene.phases().len()],
            routes: Vec::with_capacity(scene.routes().len()),
            routes_changed: false,
            remove: Vec::with_capacity(cells),
            add: Vec::with_capacity(cells),
            admissible: vec![false; edges],
            protected: vec![false; edges],
            locked: vec![false; edges],
            from: Vec::with_capacity(arc_count),
            to: Vec::with_capacity(arc_count),
            offsets: vec![0; offset_count],
            arcs: vec![0; arc_count],
            residual: vec![0; arc_count],
            parent: vec![usize::MAX; nodes],
            queue: vec![0; nodes],
            first: Vec::with_capacity(cells),
            second: Vec::with_capacity(cells),
        };
        let mut i = 0;
        while i < scene.routes().len() {
            let route = &scene.routes()[i];
            let last = route.cells.len() - 1;
            work.endpoints.push([
                route.cells[0],
                route.cells[1],
                route.cells[last - 1],
                route.cells[last],
            ]);
            work.routes.push(Route {
                circle: i,
                cells: Vec::with_capacity(cells),
            });
            i += 1;
        }
        let source = cells * 2;
        let mut v = 0;
        while v < cells {
            work.arc_pair(v * 2, v * 2 + 1);
            work.arc_pair(source, v * 2);
            v += 1;
        }
        let mut e = 0;
        while e < edges {
            let edge = scene.layout().carrier().edges()[e];
            work.arc_pair(edge.u * 2 + 1, edge.v * 2);
            work.arc_pair(edge.v * 2 + 1, edge.u * 2);
            e += 1;
        }
        let mut a = 0;
        while a < arc_count {
            let node = work.from[a];
            work.offsets[node + 1] += 1;
            a += 1;
        }
        let mut node = 0;
        while node < nodes {
            let count = work.offsets[node];
            work.offsets[node + 1] += count;
            work.parent[node] = count;
            node += 1;
        }
        let mut a = 0;
        while a < arc_count {
            let node = work.from[a];
            let slot = work.parent[node];
            work.arcs[slot] = a;
            work.parent[node] += 1;
            a += 1;
        }
        Ok(work)
    }

    fn arc_pair(&mut self, from: usize, to: usize) {
        self.from.push(from);
        self.to.push(to);
        self.from.push(to);
        self.to.push(from);
    }

    fn check_route_endpoints(cells: &[usize], ends: [usize; 4]) -> Result<(), Error> {
        let last = cells.len() - 1;
        if ends[0] != cells[0]
            || ends[1] != cells[1]
            || ends[2] != cells[last - 1]
            || ends[3] != cells[last]
        {
            Err(Error::InvalidTransition)
        } else {
            Ok(())
        }
    }

    fn check_scene(&self, scene: &Scene) -> Result<(), Error> {
        if self.epoch != scene.stamp().epoch {
            return Err(Error::StaleEpoch);
        }
        if self.cells != scene.layout().cells().len()
            || self.edges != scene.layout().carrier().edges().len()
            || self.steps.len() != scene.phases().len()
            || self.routes.len() != scene.routes().len()
        {
            return Err(Error::InsufficientWorkspace);
        }
        // Equal capacities alone do not establish carrier identity.
        let mut e = 0;
        let mut status = Ok(());
        while e < self.edges && status.is_ok() {
            let edge = scene.layout().carrier().edges()[e];
            let a = self.cells * 4 + e * 4;
            if self.from[a] != edge.u * 2 + 1 || self.to[a] != edge.v * 2 {
                status = Err(Error::InvalidCarrier);
            }
            e += 1;
        }
        status?;
        let mut r = 0;
        while r < self.routes.len() && status.is_ok() {
            status = Self::check_route_endpoints(&scene.routes()[r].cells, self.endpoints[r]);
            r += 1;
        }
        status
    }

    pub(crate) fn advance(
        &mut self,
        scene: &mut Scene,
        expected: Stamp,
        requested: &[i32],
    ) -> Result<MotionAdvance, Error> {
        // Validate the original request before subdivision, including holds and twist groups.
        scene.prepare_motion(expected, requested)?;
        self.check_scene(scene)?;
        let mut maximum = 0;
        let mut i = 0;
        while i < requested.len() {
            maximum = maximum.max(requested[i] as usize);
            i += 1;
        }
        if maximum == 0 {
            return Ok(MotionAdvance {
                event: scene.motion(expected, requested, Edit::default())?,
                divisor: 1,
            });
        }
        let mut e = 0;
        while e < self.edges {
            let edge = scene.layout().carrier().edges()[e];
            self.locked[e] =
                scene.tree().has_edge(edge) && matches!(scene.check_removal(edge), Err(_));
            e += 1;
        }
        let mut divisor = 1;
        let mut planned = false;
        let mut failure = Error::InvalidGeometry;
        let mut status = Ok(());
        while divisor <= maximum && !planned && status.is_ok() {
            let mut i = 0;
            while i < requested.len() {
                self.steps[i] = requested[i] / divisor as i32;
                i += 1;
            }
            status = scene.prepare_motion(expected, &self.steps).map(|_| ());
            if status.is_ok() {
                match self.plan(scene) {
                    Ok(()) => planned = true,
                    Err(Error::InvalidGeometry) => failure = Error::InvalidGeometry,
                    Err(Error::Disconnected) => failure = Error::Disconnected,
                    Err(Error::Occupied) => failure = Error::Occupied,
                    Err(error) => status = Err(error),
                }
            }
            if !planned && status.is_ok() {
                // Visit every distinct integer subdivision, skipping identical step vectors.
                let mut next = maximum + 1;
                let mut i = 0;
                while i < requested.len() {
                    let quotient = self.steps[i] as usize;
                    if let Some(end) = (requested[i] as usize).checked_div(quotient) {
                        next = next.min(end + 1);
                    }
                    i += 1;
                }
                divisor = next;
            }
        }
        status?;
        if !planned {
            return Err(failure);
        }
        let event = scene.motion(
            expected,
            &self.steps,
            Edit {
                remove: &self.remove,
                add: &self.add,
                routes: if self.routes_changed {
                    Some(&self.routes)
                } else {
                    None
                },
            },
        )?;
        Ok(MotionAdvance { event, divisor })
    }

    fn edge_index(&self, edge: Edge) -> Result<usize, Error> {
        let node = edge.u * 2 + 1;
        let mut pos = self.offsets[node];
        let end = self.offsets[node + 1];
        let mut found = None;
        while pos < end && found.is_none() {
            let arc = self.arcs[pos];
            if arc >= self.cells * 4 && arc & 1 == 0 && self.to[arc] == edge.v * 2 {
                found = Some((arc - self.cells * 4) / 4);
            }
            pos += 1;
        }
        found.ok_or(Error::InvalidCarrier)
    }

    // Keep shared inspection outside the planner's mutable-receiver loop context.
    fn route_admissible(&self, cells: &[usize]) -> Result<bool, Error> {
        let mut keep = true;
        let mut i = 1;
        let mut status = Ok(());
        while i < cells.len() && keep && status.is_ok() {
            let edge = Edge::new(cells[i - 1], cells[i]);
            match self.edge_index(edge) {
                Ok(index) => keep = self.admissible[index],
                Err(error) => status = Err(error),
            }
            i += 1;
        }
        status?;
        Ok(keep)
    }

    fn eligible(&self, scene: &Scene, circle: usize, cell: usize) -> bool {
        let ends = self.endpoints[circle];
        let kind = scene.layout().cells()[cell];
        match kind {
            Cell::Center { circle: owner } | Cell::Sector { circle: owner, .. } => owner == circle,
            Cell::Transition { .. } => cell == ends[1] || cell == ends[2],
            Cell::Grid { .. } => false,
        }
    }

    fn reset_flow(&mut self, scene: &Scene, circle: usize, pivot: usize) {
        let mut a = 0;
        while a < self.residual.len() {
            self.residual[a] = 0;
            a += 1;
        }
        let ends = self.endpoints[circle];
        let mut v = 0;
        while v < self.cells {
            if self.eligible(scene, circle, v) {
                self.residual[v * 4] = if v == pivot { 2 } else { 1 };
            }
            v += 1;
        }
        self.residual[ends[1] * 4 + 2] = 1;
        self.residual[ends[2] * 4 + 2] = 1;
        let mut e = 0;
        while e < self.edges {
            let edge = scene.layout().carrier().edges()[e];
            if self.admissible[e]
                && self.eligible(scene, circle, edge.u)
                && self.eligible(scene, circle, edge.v)
            {
                self.residual[self.cells * 4 + e * 4] = 1;
                self.residual[self.cells * 4 + e * 4 + 2] = 1;
            }
            e += 1;
        }
    }

    fn clear_search(&mut self, source: usize) {
        let mut i = 0;
        while i < self.parent.len() {
            self.parent[i] = usize::MAX;
            i += 1;
        }
        self.parent[source] = source;
        self.queue[0] = source;
    }

    fn residual_path(&mut self, source: usize, target: usize) -> bool {
        self.clear_search(source);
        let mut read = 0;
        let mut written = 1;
        while read < written && self.parent[target] == usize::MAX {
            let node = self.queue[read];
            let mut pos = self.offsets[node];
            while pos < self.offsets[node + 1] {
                let arc = self.arcs[pos];
                let next = self.to[arc];
                if self.residual[arc] != 0 && self.parent[next] == usize::MAX {
                    self.parent[next] = arc;
                    self.queue[written] = next;
                    written += 1;
                }
                pos += 1;
            }
            read += 1;
        }
        self.parent[target] != usize::MAX
    }

    fn augment(&mut self, source: usize, target: usize) {
        let mut node = target;
        while node != source {
            let arc = self.parent[node];
            self.residual[arc] -= 1;
            self.residual[arc ^ 1] += 1;
            node = self.from[arc];
        }
    }

    // Decompose integral flow, ignoring any residual circulation. Scratch paths run pivot -> portal.
    fn flow_path(&mut self, source: usize, target: usize) -> Result<(), Error> {
        self.clear_search(source);
        let mut read = 0;
        let mut written = 1;
        while read < written && self.parent[target] == usize::MAX {
            let node = self.queue[read];
            let mut pos = self.offsets[node];
            while pos < self.offsets[node + 1] {
                let arc = self.arcs[pos];
                let next = self.to[arc];
                if arc & 1 == 0 && self.residual[arc ^ 1] != 0 && self.parent[next] == usize::MAX {
                    self.parent[next] = arc;
                    self.queue[written] = next;
                    written += 1;
                }
                pos += 1;
            }
            read += 1;
        }
        if self.parent[target] == usize::MAX {
            return Err(Error::InvalidForest);
        }
        // Zero-length resize retains capacity and is constant-time for these no-drop elements.
        self.second.resize(0, 0);
        let mut node = target;
        while node != source {
            if node & 1 == 0 {
                self.second.push(node / 2);
            }
            let arc = self.parent[node];
            self.residual[arc ^ 1] -= 1;
            self.residual[arc] += 1;
            node = self.from[arc];
        }
        self.second.push(source / 2);
        Ok(())
    }

    fn route_through(&mut self, scene: &Scene, circle: usize, pivot: usize) -> Result<bool, Error> {
        self.reset_flow(scene, circle, pivot);
        let source = self.cells * 2;
        let target = pivot * 2 + 1;
        let mut units = 0;
        let mut possible = true;
        while units < 2 && possible {
            possible = self.residual_path(source, target);
            if possible {
                self.augment(source, target);
                units += 1;
            }
        }
        if units != 2 {
            return Ok(false);
        }
        let ends = self.endpoints[circle];
        self.flow_path(ends[1] * 2, target)?;
        self.first.resize(0, 0);
        self.first.extend_from_slice(&self.second);
        self.flow_path(ends[2] * 2, target)?;
        self.routes[circle].cells.resize(0, 0);
        self.routes[circle].cells.push(ends[0]);
        let mut i = self.first.len();
        while i > 0 {
            i -= 1;
            let cell = self.first[i];
            self.routes[circle].cells.push(cell);
        }
        let mut i = 1;
        while i < self.second.len() {
            let cell = self.second[i];
            self.routes[circle].cells.push(cell);
            i += 1;
        }
        self.routes[circle].cells.push(ends[3]);
        self.routes_changed = true;
        Ok(true)
    }

    fn plan_route(&mut self, scene: &Scene, circle: usize) -> Result<(), Error> {
        let keep = self.route_admissible(&scene.routes()[circle].cells)?;
        if keep {
            self.routes[circle].cells.resize(0, 0);
            self.routes[circle]
                .cells
                .extend_from_slice(&scene.routes()[circle].cells);
            return Ok(());
        }
        let ends = self.endpoints[circle];
        let entrance = self.edge_index(Edge::new(ends[0], ends[1]))?;
        let exit = self.edge_index(Edge::new(ends[2], ends[3]))?;
        if !self.admissible[entrance] || !self.admissible[exit] {
            return Err(Error::InvalidGeometry);
        }
        let center = scene.layout().circles()[circle].center_cell();
        let mut found = self.route_through(scene, circle, center)?;
        let mut v = 0;
        let mut status = Ok(());
        while v < self.cells && !found && status.is_ok() {
            let kind = scene.layout().cells()[v];
            if let Cell::Sector {
                circle: owner,
                ring,
                ..
            } = kind
            {
                if owner == circle && ring + 1 < scene.layout().circles()[circle].ring_count() {
                    match self.route_through(scene, circle, v) {
                        Ok(route) => found = route,
                        Err(error) => status = Err(error),
                    }
                }
            }
            v += 1;
        }
        status?;
        if found {
            Ok(())
        } else {
            Err(Error::InvalidGeometry)
        }
    }

    fn virtual_edge(&self, scene: &Scene, edge: Edge) -> bool {
        self.add.contains(&edge) || (scene.tree().has_edge(edge) && !self.remove.contains(&edge))
    }

    fn tree_path(&mut self, scene: &Scene, source: usize, target: usize) -> bool {
        self.clear_search(source);
        let mut read = 0;
        let mut written = 1;
        while read < written && self.parent[target] == usize::MAX {
            let cell = self.queue[read];
            let node = cell * 2 + 1;
            let mut pos = self.offsets[node];
            while pos < self.offsets[node + 1] {
                let arc = self.arcs[pos];
                if arc >= self.cells * 4 && arc & 1 == 0 {
                    let next = self.to[arc] / 2;
                    let edge = Edge::new(cell, next);
                    if self.parent[next] == usize::MAX && self.virtual_edge(scene, edge) {
                        self.parent[next] = cell;
                        self.queue[written] = next;
                        written += 1;
                    }
                }
                pos += 1;
            }
            read += 1;
        }
        self.parent[target] != usize::MAX
    }

    fn plan(&mut self, scene: &Scene) -> Result<(), Error> {
        self.remove.resize(0, Edge { u: 0, v: 0 });
        self.add.resize(0, Edge { u: 0, v: 0 });
        self.routes_changed = false;
        let mut e = 0;
        while e < self.edges {
            let edge = scene.layout().carrier().edges()[e];
            self.admissible[e] = scene.motion_edge(edge).is_ok();
            self.protected[e] = self.locked[e];
            e += 1;
        }
        let mut r = 0;
        let mut status = Ok(());
        while r < self.routes.len() && status.is_ok() {
            status = self.plan_route(scene, r);
            let mut i = 1;
            while i < self.routes[r].cells.len() && status.is_ok() {
                let edge = Edge::new(self.routes[r].cells[i - 1], self.routes[r].cells[i]);
                match self.edge_index(edge) {
                    Ok(e) => self.protected[e] = true,
                    Err(error) => status = Err(error),
                }
                i += 1;
            }
            r += 1;
        }
        status?;
        // Remove only endangered base edges. The remainder stays a forest, including reservations.
        let mut e = 0;
        while e < self.edges && status.is_ok() {
            let edge = scene.layout().carrier().edges()[e];
            if scene.tree().has_edge(edge) && !self.admissible[e] {
                if self.protected[e] {
                    status = Err(Error::Occupied);
                } else {
                    self.remove.push(edge);
                }
            }
            e += 1;
        }
        status?;
        // Force the complete required forest; cut one unprotected edge on each induced cycle.
        let mut r = 0;
        while r < self.routes.len() && status.is_ok() {
            let mut i = 1;
            while i < self.routes[r].cells.len() && status.is_ok() {
                let edge = Edge::new(self.routes[r].cells[i - 1], self.routes[r].cells[i]);
                if !self.virtual_edge(scene, edge) {
                    if self.tree_path(scene, edge.u, edge.v) {
                        let mut cell = edge.v;
                        let mut cut = None;
                        while cell != edge.u && cut.is_none() && status.is_ok() {
                            let parent = self.parent[cell];
                            let candidate = Edge::new(cell, parent);
                            match self.edge_index(candidate) {
                                Ok(index) => {
                                    if !self.protected[index] {
                                        cut = Some(candidate);
                                    }
                                }
                                Err(error) => status = Err(error),
                            }
                            cell = parent;
                        }
                        if status.is_ok() {
                            match cut {
                                Some(edge) => self.remove.push(edge),
                                None => status = Err(Error::Occupied),
                            }
                        }
                    }
                    if status.is_ok() {
                        self.add.push(edge);
                    }
                }
                i += 1;
            }
            r += 1;
        }
        status?;
        // Complete the forest with admissible carrier edges without replacing any remaining branch.
        let mut e = 0;
        while e < self.edges && self.add.len() < self.remove.len() {
            let edge = scene.layout().carrier().edges()[e];
            if self.admissible[e]
                && !self.virtual_edge(scene, edge)
                && !self.tree_path(scene, edge.u, edge.v)
            {
                self.add.push(edge);
            }
            e += 1;
        }
        if self.add.len() != self.remove.len() {
            return Err(Error::Disconnected);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::network_sizes;
    use crate::topology::Error;

    #[test]
    fn residual_capacity_arithmetic_rejects_overflow_before_allocation() {
        assert_eq!(network_sizes(1, 0), Ok((3, 4)));
        assert_eq!(network_sizes(usize::MAX, 0), Err(Error::Overflow));
        assert_eq!(network_sizes(1, usize::MAX), Err(Error::Overflow));
        assert_eq!(network_sizes(usize::MAX / 4, 0), Err(Error::Overflow));
        assert_eq!(
            network_sizes(1, isize::MAX as usize / 4),
            Err(Error::Overflow)
        );
    }
}
