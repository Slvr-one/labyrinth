use labyrinth_core::grid::{Geometry, GridSpec, Point, Rect};
use labyrinth_core::motion::MotionWorkspace;
use labyrinth_core::polar::{Arc, Direction, MotionMode, PolarSpec, PortalSpec};
use labyrinth_core::scene::{Edit, Layout, Route, Scene};
use labyrinth_core::shatter::Stage;
use labyrinth_core::topology::{Edge, Error};
use labyrinth_core::tree::Rng;
use labyrinth_core::walker::{Stamp, WalkerState};

struct First;
impl Rng for First {
    fn next_below(&mut self, _: usize) -> usize {
        0
    }
}
struct NoChoice;
impl Rng for NoChoice {
    fn next_below(&mut self, _: usize) -> usize {
        panic!("singleton requested randomness")
    }
}

fn geometry() -> Geometry {
    Geometry {
        viewport: Rect {
            min: Point { x: -100, y: -1500 },
            max: Point { x: 5100, y: 2500 },
        },
        obstacles: vec![],
        walker_radius: 1,
        clearance: 0,
    }
}

fn layout(
    mode: MotionMode,
    rings: usize,
    sectors: usize,
    geometry: Geometry,
) -> Result<Layout, Error> {
    let mut directions = Vec::new();
    for ring in 0..rings {
        directions.push(if ring % 2 == 0 {
            Direction::Clockwise
        } else {
            Direction::Counterclockwise
        });
    }
    Layout::new(
        GridSpec {
            columns: 5,
            rows: 1,
            origin: Point { x: 0, y: 0 },
            cell_size: 1000,
        },
        vec![PolarSpec {
            center: Point { x: 2500, y: 500 },
            center_radius: 200,
            ring_width: 200,
            sectors: vec![sectors; rings],
            directions,
            mode,
        }],
        &[
            PortalSpec {
                circle: 0,
                column: 4,
                row: 0,
                mouth: Arc {
                    start: 3712,
                    length: 768,
                },
                band: 100,
            },
            PortalSpec {
                circle: 0,
                column: 0,
                row: 0,
                mouth: Arc {
                    start: 1664,
                    length: 768,
                },
                band: 100,
            },
        ],
        geometry,
    )
}

fn route(layout: &Layout) -> Route {
    let circle = &layout.circles()[0];
    let p = layout.portals();
    let mut cells = vec![p[0].grid_cell, p[0].transition_cell];
    for ring in (0..circle.ring_count()).rev() {
        cells.push(circle.sector(ring, 0).expect("sector"));
    }
    cells.push(circle.center_cell());
    for ring in 0..circle.ring_count() {
        cells.push(
            circle
                .sector(ring, circle.spec().sectors[ring] / 2)
                .expect("opposite sector"),
        );
    }
    cells.extend_from_slice(&[p[1].transition_cell, p[1].grid_cell]);
    Route { circle: 0, cells }
}

fn scene(mode: MotionMode, occupants_on_route: &[usize], epoch: u64) -> Scene {
    let layout = layout(mode, 2, 2, geometry()).expect("layout");
    let route = route(&layout);
    let occupants: Vec<usize> = occupants_on_route
        .iter()
        .map(|index| route.cells[*index])
        .collect();
    Scene::new(layout, &[route], &occupants, 2, epoch, &mut First).expect("scene")
}

#[test]
fn singleton_is_stationary_and_checks_stamp_without_rng() {
    let layout = Layout::new(
        GridSpec {
            columns: 1,
            rows: 1,
            origin: Point { x: 0, y: 0 },
            cell_size: 100,
        },
        vec![],
        &[],
        geometry(),
    )
    .expect("singleton layout");
    let mut scene = Scene::new(layout, &[], &[0], 1, 0, &mut NoChoice).expect("singleton");
    let initial = scene.stamp();
    assert_eq!(
        scene.begin_crossing(initial, 0, 0, 1),
        Err(Error::InvalidTransition)
    );
    assert_eq!(scene.stamp(), initial);
    scene.tick(initial, 100).expect("stationary tick");
    assert_eq!(scene.walkers()[0].cell(), 0);
    assert_eq!(scene.tree().parents(), &[0]);
}

#[test]
fn replaced_grid_cells_have_no_ids_and_routes_really_cross_interior() {
    for mode in [
        MotionMode::Spinning,
        MotionMode::Twisting {
            amplitude: 32,
            max_relative: 64,
        },
    ] {
        let mut scene = scene(mode, &[0], 1);
        assert_eq!(scene.layout().grid().cell(2, 0), None);
        assert_eq!(scene.layout().grid().cell(1, 0), None);
        let route = scene.routes()[0].cells.clone();
        let center = scene.layout().circles()[0].center_cell();
        assert!(route.contains(&center));
        let mut wall = 0;
        for target in &route[1..] {
            let source = scene.walkers()[0].cell();
            scene
                .begin_crossing(scene.stamp(), 0, *target, 10)
                .expect("admission");
            wall += 5;
            scene.tick(scene.stamp(), wall).expect("half crossing");
            assert_eq!(
                scene.walkers()[0].cell(),
                source,
                "ownership stays source-local"
            );
            wall += 5;
            scene.tick(scene.stamp(), wall).expect("complete crossing");
            assert_eq!(
                scene.walkers()[0].cell(),
                *target,
                "target ownership precedes hold release"
            );
            assert!(scene.holds().iter().all(|count| *count == 0));
        }
        assert_ne!(route[0], scene.walkers()[0].cell());
    }
}

#[test]
fn invalid_and_cyclic_routes_are_rejected_before_publication() {
    let source = layout(MotionMode::Spinning, 2, 2, geometry()).expect("layout");
    let mut cyclic = route(&source);
    cyclic.cells[4] = cyclic.cells[2];
    assert!(matches!(
        Scene::new(source, &[cyclic], &[], 0, 1, &mut First),
        Err(Error::InvalidForest)
    ));
    let source = layout(MotionMode::Spinning, 2, 2, geometry()).expect("layout");
    let mut invalid = route(&source);
    invalid.cells[0] = invalid.cells[8];
    assert!(Scene::new(source, &[invalid], &[], 0, 1, &mut First).is_err());
    let source = layout(MotionMode::Spinning, 2, 2, geometry()).expect("layout");
    assert!(Scene::new(source, &[], &[], 0, 1, &mut First).is_err());
}

#[test]
fn clipping_and_obstacles_reject_the_entire_swept_corridor() {
    let mut clipped = geometry();
    clipped.viewport.min.y = -100;
    let source = layout(MotionMode::Spinning, 2, 2, clipped).expect("exterior portals fit");
    let required = route(&source);
    assert!(matches!(
        Scene::new(source, &[required], &[], 0, 1, &mut First),
        Err(Error::InvalidGeometry)
    ));
    let mut obstructed = geometry();
    obstructed.obstacles.push(Rect {
        min: Point { x: 2450, y: 450 },
        max: Point { x: 2550, y: 550 },
    });
    let source = layout(MotionMode::Spinning, 2, 2, obstructed).expect("portals remain clear");
    let required = route(&source);
    assert!(matches!(
        Scene::new(source, &[required], &[], 0, 1, &mut First),
        Err(Error::InvalidGeometry)
    ));
}

#[test]
fn reservations_share_reference_counted_holds_and_survive_unrelated_revisions() {
    let mut scene = scene(MotionMode::Spinning, &[3, 5], 9);
    let route = scene.routes()[0].cells.clone();
    let a = scene
        .begin_crossing(scene.stamp(), 0, route[2], 5)
        .expect("first crossing");
    let old = scene.stamp();
    let b = scene
        .begin_crossing(old, 1, route[6], 10)
        .expect("second crossing");
    assert_eq!(scene.holds(), &[2, 2]);
    assert!(scene.reservation(a).is_ok());
    assert_eq!(
        scene.motion(old, &[1, 1], Edit::default()),
        Err(Error::StaleRevision)
    );
    let stamp = scene.stamp();
    let parents = scene.tree().parents().to_vec();
    assert_eq!(
        scene.motion(stamp, &[128, 128], Edit::default()),
        Err(Error::Occupied)
    );
    assert_eq!(scene.stamp(), stamp);
    assert_eq!(scene.phases(), &[0, 0]);
    assert_eq!(scene.tree().parents(), parents);
    scene.tick(stamp, 5).expect("first completion");
    assert_eq!(scene.holds(), &[1, 1]);
    assert!(scene.reservation(a).is_err());
    assert_eq!(scene.reservation(b).expect("second still live").elapsed, 5);
    scene.tick(scene.stamp(), 10).expect("second completion");
    assert_eq!(scene.holds(), &[0, 0]);
    scene
        .motion(scene.stamp(), &[128, 128], Edit::default())
        .expect("motion resumes without catch-up");
}

#[test]
fn reserved_corridors_cannot_be_closed_even_with_valid_tree_edits() {
    let mut scene = scene(MotionMode::Spinning, &[3], 1);
    let route = scene.routes()[0].cells.clone();
    scene
        .begin_crossing(scene.stamp(), 0, route[2], 10)
        .expect("crossing");
    let stamp = scene.stamp();
    let remove = [Edge::new(route[2], route[3])];
    let add = [Edge::new(route[2], route[5])];
    assert_eq!(
        scene.motion(
            stamp,
            &[0, 0],
            Edit {
                remove: &remove,
                add: &add,
                routes: None
            }
        ),
        Err(Error::Occupied)
    );
    assert_eq!(scene.stamp(), stamp);
    assert!(scene.tree().has_edge(remove[0]));
}

#[test]
fn shatter_drains_then_parks_hides_and_reopens_at_one_deadline() {
    let mut scene = scene(MotionMode::Spinning, &[3, 2], 1);
    let route = scene.routes()[0].cells.clone();
    let target = route[2];
    scene
        .begin_crossing(scene.stamp(), 0, target, 10)
        .expect("accepted crossing");
    scene.tick(scene.stamp(), 4).expect("in flight");
    let patch = scene
        .begin_shatter(scene.stamp(), &[target])
        .expect("close admission");
    assert_eq!(scene.patch_stage(patch), Ok(Stage::Draining));
    assert_eq!(
        scene.begin_shatter(scene.stamp(), &[target]),
        Err(Error::Occupied)
    );
    assert_eq!(scene.hide_patch(scene.stamp(), patch), Err(Error::Occupied));
    assert_eq!(
        scene.begin_crossing(scene.stamp(), 1, route[3], 10),
        Err(Error::Occupied)
    );
    scene.tick(scene.stamp(), 10).expect("drain completes");
    assert_eq!(scene.walkers()[0].cell(), target);
    assert_eq!(scene.patch_stage(patch), Ok(Stage::Parked));
    assert_eq!(scene.walkers()[0].state(), WalkerState::Parked);
    assert_eq!(scene.walkers()[1].state(), WalkerState::Parked);
    assert_eq!(
        scene.scatter_patch(scene.stamp(), patch, 5),
        Err(Error::InvalidTransition)
    );
    scene
        .hide_patch(scene.stamp(), patch)
        .expect("hide before displacement");
    scene
        .scatter_patch(scene.stamp(), patch, 5)
        .expect("fragments move only while hidden");
    assert_eq!(
        scene.motion(scene.stamp(), &[1, 1], Edit::default()),
        Err(Error::Occupied)
    );
    assert_eq!(
        scene.reform_patch(scene.stamp(), patch, 5, Edit::default()),
        Err(Error::InvalidTransition)
    );
    scene.tick(scene.stamp(), 15).expect("scatter deadline");
    scene
        .reform_patch(scene.stamp(), patch, 5, Edit::default())
        .expect("checked patch publication");
    scene.tick(scene.stamp(), 19).expect("before reopen");
    assert_eq!(scene.walkers()[0].state(), WalkerState::Hidden);
    assert_eq!(scene.walkers()[1].state(), WalkerState::Hidden);
    scene.tick(scene.stamp(), 20).expect("shared reopen");
    assert_eq!(scene.walkers()[0].state(), WalkerState::Ready);
    assert_eq!(scene.walkers()[1].state(), WalkerState::Ready);
    assert!(
        scene.patch_stage(patch).is_err(),
        "retired patch handles cannot be reused"
    );
}

#[test]
fn suspension_retains_fraction_and_holds_without_wall_time_catch_up() {
    let mut scene = scene(MotionMode::Spinning, &[3], 1);
    let target = scene.routes()[0].cells[2];
    let token = scene
        .begin_crossing(scene.stamp(), 0, target, 10)
        .expect("crossing");
    scene.tick(scene.stamp(), 4).expect("fraction");
    let position = scene.walker_pose(0).expect("position");
    scene.suspend(scene.stamp(), 4).expect("suspend");
    scene.tick(scene.stamp(), 1000).expect("hidden frame");
    assert_eq!(scene.clock(), 4);
    assert_eq!(
        scene
            .reservation(token)
            .expect("retained reservation")
            .elapsed,
        4
    );
    assert_eq!(scene.walker_pose(0).expect("frozen pose"), position);
    assert_eq!(scene.holds(), &[1, 1]);
    scene.resume(scene.stamp(), 2000).expect("resume");
    scene
        .tick(scene.stamp(), 2005)
        .expect("five new milliseconds");
    assert_eq!(scene.reservation(token).expect("not caught up").elapsed, 9);
    scene.tick(scene.stamp(), 2006).expect("finish");
    assert_eq!(scene.walkers()[0].cell(), target);
}

#[test]
fn only_latest_validated_epoch_can_publish_and_old_crossings_are_disposed() {
    let mut live = scene(MotionMode::Spinning, &[3], 10);
    let target = live.routes()[0].cells[2];
    let token = live
        .begin_crossing(live.stamp(), 0, target, 100)
        .expect("crossing");
    let older = live.request_layout(live.stamp()).expect("request");
    let latest = live
        .request_layout(live.stamp())
        .expect("superseding request");
    let stamp = live.stamp();
    assert_eq!(
        live.publish_layout(older, scene(MotionMode::Spinning, &[0], older)),
        Err(Error::StaleEpoch)
    );
    assert_eq!(live.stamp(), stamp);
    live.tick(stamp, 1000).expect("frozen while validating");
    assert_eq!(
        live.reservation(token)
            .expect("old crossing retained")
            .elapsed,
        0
    );
    live.suspend(live.stamp(), 1000)
        .expect("suspend while replacing");
    let retired = live
        .publish_layout(latest, scene(MotionMode::Spinning, &[0], latest))
        .expect("atomic replacement");
    assert_eq!(retired.released_reservations, 1);
    assert_eq!(retired.terminated_walkers, 1);
    assert_eq!(live.holds(), &[0, 0]);
    assert!(live.is_suspended());
    assert_eq!(live.reservation(token), Err(Error::StaleEpoch));
    assert_eq!(
        live.tick(
            Stamp {
                epoch: 10,
                revision: 0
            },
            1001
        ),
        Err(Error::StaleEpoch)
    );
}

#[test]
fn rejected_epoch_resumes_existing_crossing_only_when_old_layout_still_fits() {
    let mut live = scene(MotionMode::Spinning, &[3], 1);
    let target = live.routes()[0].cells[2];
    let token = live
        .begin_crossing(live.stamp(), 0, target, 10)
        .expect("crossing");
    let request = live.request_layout(live.stamp()).expect("request");
    live.tick(live.stamp(), 500).expect("freeze");
    live.reject_layout(request, geometry().viewport)
        .expect("resume original epoch");
    live.resume(live.stamp(), 500)
        .expect("anchor replacement cancellation");
    live.tick(live.stamp(), 505).expect("new time only");
    assert_eq!(live.reservation(token).expect("continuation").elapsed, 5);
    let request = live.request_layout(live.stamp()).expect("new request");
    live.reject_layout(
        request,
        Rect {
            min: Point { x: 0, y: 0 },
            max: Point { x: 100, y: 100 },
        },
    )
    .expect("inert rejection cleanup");
    assert!(live.is_inactive());
    live.tick(live.stamp(), 10000).expect("inert frame");
    assert_eq!(
        live.reservation(token)
            .expect("safe retained crossing")
            .elapsed,
        5
    );
}

#[test]
fn multiple_rings_and_sector_counts_are_not_fixture_specific() {
    for mode in [
        MotionMode::Spinning,
        MotionMode::Twisting {
            amplitude: 16,
            max_relative: 32,
        },
    ] {
        let source = layout(mode, 3, 4, geometry()).expect("three-ring geometry");
        let route = route(&source);
        let occupant = route.cells[3];
        let mut scene =
            Scene::new(source, &[route], &[occupant], 1, 1, &mut First).expect("three-ring scene");
        let local = scene.walkers()[0].local_pose();
        let initial = scene.walker_pose(0).expect("local pose");
        scene
            .motion(scene.stamp(), &[128, 128, 128], Edit::default())
            .expect("safe shared interval");
        assert_eq!(scene.walkers()[0].local_pose(), local);
        assert_ne!(scene.walker_pose(0).expect("riding pose"), initial);
        let circle = &scene.layout().circles()[0];
        for ring in 0..circle.ring_count() {
            let radius = circle.spec().center_radius
                + ring as i32 * circle.spec().ring_width
                + circle.spec().ring_width / 2;
            assert_eq!(
                circle
                    .offset_at(radius, 100, scene.phases())
                    .expect("ring-center offset"),
                circle
                    .ring_offset(ring, scene.phases())
                    .expect("ring phase")
            );
        }
        scene
            .tree()
            .validate(scene.layout().carrier())
            .expect("connected tree");
    }
}

#[test]
fn twist_rejects_excess_shear_and_nonshared_phase_updates() {
    assert!(layout(
        MotionMode::Twisting {
            amplitude: 512,
            max_relative: 1024
        },
        2,
        2,
        geometry()
    )
    .is_err());
    let mut scene = scene(
        MotionMode::Twisting {
            amplitude: 32,
            max_relative: 64,
        },
        &[],
        1,
    );
    let stamp = scene.stamp();
    assert_eq!(
        scene.motion(stamp, &[128, 0], Edit::default()),
        Err(Error::InvalidGeometry)
    );
    assert_eq!(scene.stamp(), stamp);
    assert_eq!(scene.phases(), &[0, 0]);
}

#[test]
fn a_canceled_layout_without_intermediate_frames_does_not_catch_up() {
    let mut live = scene(MotionMode::Spinning, &[3], 1);
    let target = live.routes()[0].cells[2];
    let token = live
        .begin_crossing(live.stamp(), 0, target, 10)
        .expect("crossing");
    let request = live.request_layout(live.stamp()).expect("request");
    live.reject_layout(request, geometry().viewport)
        .expect("cancel");
    live.tick(live.stamp(), 10000)
        .expect("reanchor without simulation debt");
    assert_eq!(live.reservation(token).expect("still crossing").elapsed, 0);
    live.tick(live.stamp(), 10005)
        .expect("five new milliseconds");
    assert_eq!(live.reservation(token).expect("continuation").elapsed, 5);
}

#[test]
fn integer_rotation_stays_within_the_declared_rounding_guard() {
    for radius in [1, 1000, 1_000_000] {
        for angle in 0..labyrinth_core::polar::TURN {
            let point = labyrinth_core::polar::project(Point { x: 0, y: 0 }, radius, angle)
                .expect("bounded projection");
            let radians =
                f64::from(angle) * core::f64::consts::TAU / f64::from(labyrinth_core::polar::TURN);
            assert!(
                (f64::from(point.x) - f64::from(radius) * radians.cos()).abs() < 2.0,
                "x rounding at radius {radius}, angle {angle}"
            );
            assert!(
                (f64::from(point.y) - f64::from(radius) * radians.sin()).abs() < 2.0,
                "y rounding at radius {radius}, angle {angle}"
            );
        }
    }
    assert_eq!(
        labyrinth_core::polar::project(Point { x: 0, y: 0 }, -1, 0),
        Err(Error::InvalidGeometry)
    );
}

fn assert_motion_scene(scene: &Scene) {
    scene
        .tree()
        .validate(scene.layout().carrier())
        .expect("planner retains a tree");
    for (circle, route) in scene.routes().iter().enumerate() {
        assert_eq!(route.circle, circle);
        let mut interior = false;
        for (i, cell) in route.cells.iter().copied().enumerate() {
            assert!(!route.cells[..i].contains(&cell), "certificate is simple");
            match scene.layout().cells()[cell] {
                labyrinth_core::scene::Cell::Center { circle: owner } => {
                    assert_eq!(owner, circle);
                    interior = true;
                }
                labyrinth_core::scene::Cell::Sector {
                    circle: owner,
                    ring,
                    ..
                } => {
                    assert_eq!(owner, circle);
                    interior |= ring + 1 < scene.layout().circles()[circle].ring_count();
                }
                _ => {}
            }
        }
        assert!(interior, "an outer-only detour is not a route");
        for pair in route.cells.windows(2) {
            assert!(scene.tree().has_edge(Edge::new(pair[0], pair[1])));
        }
    }
    for (cell, parent) in scene.tree().parents().iter().copied().enumerate() {
        if cell != parent {
            scene
                .doorway_bounds(Edge::new(cell, parent))
                .expect("all published edges admit geometry");
        }
    }
}

fn run_three_periods(scene: &mut Scene, request: i32) -> (usize, usize) {
    let mut work = MotionWorkspace::new(scene).expect("planner workspace");
    let endpoints: Vec<_> = scene
        .routes()
        .iter()
        .map(|route| (route.cells[0], *route.cells.last().expect("route endpoint")))
        .collect();
    let grid_edges: Vec<_> = scene
        .tree()
        .parents()
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(cell, parent)| {
            if cell != parent
                && matches!(
                    scene.layout().cells()[cell],
                    labyrinth_core::scene::Cell::Grid { .. }
                )
                && matches!(
                    scene.layout().cells()[parent],
                    labyrinth_core::scene::Cell::Grid { .. }
                )
            {
                Some(Edge::new(cell, parent))
            } else {
                None
            }
        })
        .collect();
    let mut elapsed = 0;
    let mut replacements = 0;
    let mut subdivisions = 0;
    while elapsed < labyrinth_core::polar::TURN * 3 {
        let increment = request.min(labyrinth_core::polar::TURN * 3 - elapsed);
        let steps = vec![increment; scene.phases().len()];
        let stamp = scene.stamp();
        let advance = scene
            .advance_motion(stamp, &steps, &mut work)
            .unwrap_or_else(|error| panic!("planner stalled at elapsed {elapsed}: {error:?}"));
        assert!(advance.divisor > 0 && advance.divisor <= increment as usize);
        let consumed = increment / advance.divisor as i32;
        assert!(consumed > 0);
        elapsed += consumed;
        replacements += advance.event.replaced;
        subdivisions += usize::from(advance.divisor > 1);
        assert_eq!(advance.event.stamp, scene.stamp());
        assert_eq!(
            scene.stamp().revision,
            stamp.revision + 1,
            "exactly one publication"
        );
        assert!(scene
            .phases()
            .iter()
            .all(|phase| *phase == elapsed % labyrinth_core::polar::TURN));
        assert_motion_scene(scene);
        for (route, ends) in scene.routes().iter().zip(&endpoints) {
            assert_eq!(
                (route.cells[0], *route.cells.last().expect("endpoint")),
                *ends
            );
        }
        for edge in &grid_edges {
            assert!(
                scene.tree().has_edge(*edge),
                "unrelated valid grid branch was replaced"
            );
        }
    }
    assert!(scene.phases().iter().all(|phase| *phase == 0));
    (replacements, subdivisions)
}

#[test]
fn production_planner_completes_periods_without_a_hamiltonian_route() {
    for (rings, sectors) in [(2, 2), (3, 4), (4, 8)] {
        for mode in [
            MotionMode::Spinning,
            MotionMode::Twisting {
                amplitude: 16,
                max_relative: 32,
            },
        ] {
            let source = layout(mode, rings, sectors, geometry()).expect("generic layout");
            let certificate = route(&source);
            if sectors > 2 {
                assert!(
                    certificate.cells.len() < source.cells().len(),
                    "non-Hamiltonian fixture"
                );
            }
            let mut scene =
                Scene::new(source, &[certificate], &[], 0, 1, &mut First).expect("generic scene");
            let (replacements, _) = run_three_periods(&mut scene, 128);
            if mode == MotionMode::Spinning {
                assert!(
                    replacements > 0,
                    "ordinary spins must replace endangered edges"
                );
            }
        }
    }
}

fn multiple_circle_scene(occupants: bool, epoch: u64) -> Scene {
    let sectors = [vec![4, 8, 4], vec![8, 4, 8, 8]];
    let mut specs = Vec::new();
    let mut portals = Vec::new();
    for (circle, counts) in sectors.iter().enumerate() {
        specs.push(PolarSpec {
            center: Point {
                x: 2500 + circle as i32 * 6000,
                y: 1500,
            },
            center_radius: 200,
            ring_width: 200,
            sectors: counts.clone(),
            directions: (0..counts.len())
                .map(|ring| {
                    if ring % 2 == 0 {
                        Direction::Clockwise
                    } else {
                        Direction::Counterclockwise
                    }
                })
                .collect(),
            mode: MotionMode::Spinning,
        });
        portals.push(PortalSpec {
            circle,
            column: 4 + circle * 6,
            row: 1,
            mouth: Arc {
                start: 3712,
                length: 768,
            },
            band: 100,
        });
        portals.push(PortalSpec {
            circle,
            column: circle * 6,
            row: 1,
            mouth: Arc {
                start: 1664,
                length: 768,
            },
            band: 100,
        });
    }
    let source = Layout::new(
        GridSpec {
            columns: 12,
            rows: 3,
            origin: Point { x: 0, y: 0 },
            cell_size: 1000,
        },
        specs,
        &portals,
        Geometry {
            viewport: Rect {
                min: Point { x: -100, y: -1000 },
                max: Point { x: 12100, y: 4000 },
            },
            obstacles: vec![],
            walker_radius: 1,
            clearance: 0,
        },
    )
    .expect("multiple-circle geometry with unrelated grid branches");
    let mut routes = Vec::new();
    for (ci, circle) in source.circles().iter().enumerate() {
        let a = source.portals()[ci * 2];
        let b = source.portals()[ci * 2 + 1];
        let mut cells = vec![a.grid_cell, a.transition_cell];
        for ring in (0..circle.ring_count()).rev() {
            cells.push(circle.sector(ring, 0).expect("sector"));
        }
        cells.push(circle.center_cell());
        for ring in 0..circle.ring_count() {
            cells.push(
                circle
                    .sector(ring, circle.spec().sectors[ring] / 2)
                    .expect("opposite sector"),
            );
        }
        cells.extend_from_slice(&[b.transition_cell, b.grid_cell]);
        routes.push(Route { circle: ci, cells });
    }
    let occupants = if occupants {
        vec![routes[0].cells[3]]
    } else {
        vec![]
    };
    Scene::new(source, &routes, &occupants, 1, epoch, &mut First).expect("multiple-circle scene")
}

#[test]
fn production_planner_handles_multiple_circles_unequal_rings_and_grid_branches() {
    let mut scene = multiple_circle_scene(false, 4);
    assert_eq!(scene.layout().circles().len(), 2);
    let (replacements, subdivisions) = run_three_periods(&mut scene, 512);
    assert!(replacements > 0);
    assert!(
        subdivisions > 0,
        "long requests must report safe positive prefixes"
    );
}

#[test]
fn production_planner_reports_partial_steps_without_partial_publications() {
    let source = layout(MotionMode::Spinning, 4, 8, geometry()).expect("layout");
    let certificate = route(&source);
    let mut scene = Scene::new(source, &[certificate], &[], 0, 1, &mut First).expect("scene");
    let mut work = MotionWorkspace::new(&scene).expect("workspace");
    let stamp = scene.stamp();
    let advance = scene
        .advance_motion(stamp, &[512; 4], &mut work)
        .expect("positive prefix");
    assert!(
        advance.divisor > 1,
        "opposite ring spins cross more than one doorway event"
    );
    assert!(512 / advance.divisor as i32 > 0);
    assert_eq!(scene.phases(), &[512 / advance.divisor as i32; 4]);
    assert_eq!(scene.stamp().revision, stamp.revision + 1);
    assert_motion_scene(&scene);
}

#[test]
fn production_planner_preserves_reservations_and_moves_unrelated_circles() {
    let mut scene = multiple_circle_scene(true, 8);
    let mut work = MotionWorkspace::new(&scene).expect("workspace");
    let route = scene.routes()[0].cells.clone();
    let target = route[2];
    let token = scene
        .begin_crossing(scene.stamp(), 0, target, 10)
        .expect("reserve first circle");
    let stamp = scene.stamp();
    let parents = scene.tree().parents().to_vec();
    let phases = scene.phases().to_vec();
    let holds = scene.holds().to_vec();
    assert_eq!(
        scene.advance_motion(stamp, &[128; 7], &mut work),
        Err(Error::Occupied)
    );
    assert_eq!(scene.stamp(), stamp);
    assert_eq!(scene.tree().parents(), parents);
    assert_eq!(scene.phases(), phases);
    assert_eq!(scene.holds(), holds);
    for _ in 0..40 {
        scene
            .advance_motion(scene.stamp(), &[0, 0, 0, 128, 128, 128, 128], &mut work)
            .expect("unreserved circle advances through boundary events");
        assert!(scene.reservation(token).is_ok());
        assert_eq!(scene.routes()[0].cells, route);
        assert_eq!(&scene.phases()[..3], &[0; 3]);
        assert_eq!(scene.holds(), holds);
        assert_motion_scene(&scene);
    }
    scene
        .tick(scene.stamp(), 10)
        .expect("accepted crossing completes first");
    assert_eq!(scene.walkers()[0].cell(), target);
    assert!(scene.reservation(token).is_err());
    assert!(scene.holds().iter().all(|count| *count == 0));
    scene
        .advance_motion(scene.stamp(), &[128; 7], &mut work)
        .expect("held circle resumes");
    assert!(scene.phases()[0] > 0);
    assert_motion_scene(&scene);
}

#[test]
fn production_planner_rejections_preserve_identity_and_zero_steps_keep_revisions() {
    let mut scene = scene(MotionMode::Spinning, &[], 10);
    let mut work = MotionWorkspace::new(&scene).expect("workspace");
    let stamp = scene.stamp();
    let parents = scene.tree().parents().to_vec();
    let routes = scene.routes().to_vec();
    for (steps, error) in [
        (vec![1], Error::InvalidSize),
        (vec![-1, 0], Error::InvalidGeometry),
        (vec![i32::MAX, i32::MAX], Error::InvalidGeometry),
        (vec![513, 513], Error::InvalidGeometry),
    ] {
        assert_eq!(scene.advance_motion(stamp, &steps, &mut work), Err(error));
        assert_eq!(scene.stamp(), stamp);
        assert_eq!(scene.tree().parents(), parents);
        assert_eq!(scene.phases(), &[0, 0]);
        assert_eq!(scene.routes(), routes);
    }
    let stale = Stamp {
        epoch: 9,
        revision: stamp.revision,
    };
    assert_eq!(
        scene.advance_motion(stale, &[0, 0], &mut work),
        Err(Error::StaleEpoch)
    );
    let zero = scene
        .advance_motion(stamp, &[0, 0], &mut work)
        .expect("zero fast path");
    assert_eq!(zero.divisor, 1);
    assert_eq!(zero.event.replaced, 0);
    assert_eq!(zero.event.moving_doorways, 0);
    assert_eq!(scene.stamp().revision, stamp.revision + 1);
    assert_eq!(scene.tree().parents(), parents);
    assert_eq!(scene.routes(), routes);
    assert_eq!(
        scene.advance_motion(stamp, &[0, 0], &mut work),
        Err(Error::StaleRevision)
    );
    scene.suspend(scene.stamp(), 0).expect("suspend");
    let frozen = scene.stamp();
    assert_eq!(
        scene.advance_motion(frozen, &[0, 0], &mut work),
        Err(Error::InvalidTransition)
    );
    assert_eq!(scene.stamp(), frozen);
}

#[test]
fn production_planner_rejects_stale_and_undersized_workspaces() {
    let source = scene(MotionMode::Spinning, &[], 1);
    let mut work = MotionWorkspace::new(&source).expect("workspace");
    let mut larger = multiple_circle_scene(false, 1);
    let stamp = larger.stamp();
    let parents = larger.tree().parents().to_vec();
    assert_eq!(
        larger.advance_motion(stamp, &[128; 7], &mut work),
        Err(Error::InsufficientWorkspace)
    );
    assert_eq!(larger.stamp(), stamp);
    assert_eq!(larger.tree().parents(), parents);
    let mut replacement = scene(MotionMode::Spinning, &[], 2);
    let stamp = replacement.stamp();
    assert_eq!(
        replacement.advance_motion(stamp, &[0, 0], &mut work),
        Err(Error::StaleEpoch)
    );
    assert_eq!(replacement.stamp(), stamp);
}

#[test]
fn production_planner_checks_endpoint_binding_and_twist_groups_before_subdividing() {
    let original = scene(MotionMode::Spinning, &[], 1);
    let mut work = MotionWorkspace::new(&original).expect("workspace");
    let source = layout(MotionMode::Spinning, 2, 2, geometry()).expect("layout");
    let mut certificate = route(&source);
    certificate.cells.reverse();
    let mut reversed =
        Scene::new(source, &[certificate], &[], 0, 1, &mut First).expect("reversed route");
    let stamp = reversed.stamp();
    let parents = reversed.tree().parents().to_vec();
    assert_eq!(
        reversed.advance_motion(stamp, &[128, 128], &mut work),
        Err(Error::InvalidTransition)
    );
    assert_eq!(reversed.stamp(), stamp);
    assert_eq!(reversed.tree().parents(), parents);

    let mut twisting = scene(
        MotionMode::Twisting {
            amplitude: 16,
            max_relative: 32,
        },
        &[],
        2,
    );
    let mut work = MotionWorkspace::new(&twisting).expect("twist workspace");
    let stamp = twisting.stamp();
    assert_eq!(
        twisting.advance_motion(stamp, &[512, 511], &mut work),
        Err(Error::InvalidGeometry)
    );
    assert_eq!(twisting.stamp(), stamp);
    assert_eq!(twisting.phases(), &[0, 0]);
}

#[test]
fn production_planner_supports_an_empty_transform_set() {
    let source = Layout::new(
        GridSpec {
            columns: 1,
            rows: 1,
            origin: Point { x: 0, y: 0 },
            cell_size: 100,
        },
        vec![],
        &[],
        geometry(),
    )
    .expect("singleton layout");
    let mut scene = Scene::new(source, &[], &[], 0, 1, &mut NoChoice).expect("singleton scene");
    let mut work = MotionWorkspace::new(&scene).expect("singleton workspace");
    let stamp = scene.stamp();
    let advance = scene
        .advance_motion(stamp, &[], &mut work)
        .expect("stationary publication");
    assert_eq!(advance.divisor, 1);
    assert_eq!(advance.event.replaced, 0);
    assert_eq!(advance.event.moving_doorways, 0);
    assert_eq!(scene.stamp().revision, stamp.revision + 1);
    assert_eq!(scene.tree().parents(), &[0]);
}

#[test]
fn spinning_constructor_rejects_unavoidable_inter_ring_gaps() {
    // Width 128 admits the initial doorway (minimum 82 at radius 300), but opposite
    // phase-32 spins leave only 64 units of overlap for every inter-ring pairing.
    let source = match layout(MotionMode::Spinning, 2, 32, geometry()) {
        Ok(source) => source,
        Err(error) => {
            assert_eq!(error, Error::InvalidGeometry);
            return;
        }
    };
    let certificate = route(&source);
    assert!(
        matches!(Scene::new(source, &[certificate], &[], 0, 1, &mut First), Err(Error::InvalidGeometry)),
        "construction must reject geometry that no boundary planner can keep connected while spinning"
    );
}

#[test]
fn spinning_clearance_bounds_allow_resized_high_sector_counts() {
    let source = Layout::new(
        GridSpec {
            columns: 5,
            rows: 1,
            origin: Point { x: 0, y: 0 },
            cell_size: 1000,
        },
        vec![PolarSpec {
            center: Point { x: 2500, y: 500 },
            center_radius: 400,
            ring_width: 400,
            sectors: vec![32, 32],
            directions: vec![Direction::Clockwise, Direction::Counterclockwise],
            mode: MotionMode::Spinning,
        }],
        &[
            PortalSpec {
                circle: 0,
                column: 4,
                row: 0,
                mouth: Arc {
                    start: 3712,
                    length: 768,
                },
                band: 100,
            },
            PortalSpec {
                circle: 0,
                column: 0,
                row: 0,
                mouth: Arc {
                    start: 1664,
                    length: 768,
                },
                band: 100,
            },
        ],
        geometry(),
    )
    .expect("clearance depends on physical radius, not a fixed count cap");
    let certificate = route(&source);
    let mut scene =
        Scene::new(source, &[certificate], &[], 0, 1, &mut First).expect("resized scene");
    let (replacements, subdivisions) = run_three_periods(&mut scene, 128);
    assert!(replacements > 0);
    assert!(subdivisions > 0);
}

#[test]
fn spinning_portal_pair_cannot_collapse_to_one_outer_sector() {
    let source = Layout::new(
        GridSpec {
            columns: 5,
            rows: 5,
            origin: Point { x: 0, y: 0 },
            cell_size: 1000,
        },
        vec![PolarSpec {
            center: Point { x: 2500, y: 2500 },
            center_radius: 200,
            ring_width: 200,
            sectors: vec![2, 2],
            directions: vec![Direction::Clockwise, Direction::Counterclockwise],
            mode: MotionMode::Spinning,
        }],
        &[
            PortalSpec {
                circle: 0,
                column: 4,
                row: 2,
                mouth: Arc {
                    start: 3712,
                    length: 768,
                },
                band: 100,
            },
            PortalSpec {
                circle: 0,
                column: 2,
                row: 0,
                mouth: Arc {
                    start: 2688,
                    length: 768,
                },
                band: 100,
            },
        ],
        Geometry {
            viewport: Rect {
                min: Point { x: -100, y: -100 },
                max: Point { x: 5100, y: 5100 },
            },
            obstacles: vec![],
            walker_radius: 1,
            clearance: 0,
        },
    )
    .expect("individually valid east and north portals");
    let certificate = route(&source);
    // Initially the east portal can use sector 0 and north sector 1. Later both mouths
    // lie strictly inside sector 1, so no simple route can enter the actual interior.
    assert!(
        matches!(
            Scene::new(source, &[certificate], &[], 0, 1, &mut First),
            Err(Error::InvalidGeometry)
        ),
        "the chosen pair must retain a two-matching, not merely one neighbor per portal"
    );
    let mut opposite = scene(MotionMode::Spinning, &[], 1);
    let mut work =
        MotionWorkspace::new(&opposite).expect("opposite portals admit overlapping neighbor sets");
    opposite
        .advance_motion(opposite.stamp(), &[128, 128], &mut work)
        .expect("ordinary fixture remains accepted");
}
