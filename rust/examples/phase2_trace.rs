use labyrinth_core::grid::{Geometry, GridSpec, Point, Rect};
use labyrinth_core::motion::MotionWorkspace;
use labyrinth_core::polar::{Arc, Direction, MotionMode, PolarSpec, PortalSpec, TURN};
use labyrinth_core::scene::{Edit, Layout, Route, Scene};
use labyrinth_core::shatter::Stage;
use labyrinth_core::topology::Error;
use labyrinth_core::tree::Rng;
use labyrinth_core::walker::{Stamp, WalkerState};

const SEED: u64 = 0x6a09_e667_f3bc_c909;

struct Seeded(u64);
impl Rng for Seeded {
    fn next_below(&mut self, bound: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % bound as u64) as usize
    }
}

fn layout(mode: MotionMode) -> Result<Layout, Error> {
    Layout::new(
        GridSpec {
            columns: 5,
            rows: 3,
            origin: Point { x: 0, y: 0 },
            cell_size: 1000,
        },
        vec![PolarSpec {
            center: Point { x: 2500, y: 1500 },
            center_radius: 200,
            ring_width: 200,
            sectors: vec![2, 2],
            directions: vec![Direction::Clockwise, Direction::Counterclockwise],
            mode,
        }],
        &[
            PortalSpec {
                circle: 0,
                column: 4,
                row: 1,
                mouth: Arc {
                    start: 3712,
                    length: 768,
                },
                band: 100,
            },
            PortalSpec {
                circle: 0,
                column: 0,
                row: 1,
                mouth: Arc {
                    start: 1664,
                    length: 768,
                },
                band: 100,
            },
        ],
        Geometry {
            viewport: Rect {
                min: Point { x: -100, y: -400 },
                max: Point { x: 5100, y: 3400 },
            },
            obstacles: vec![],
            walker_radius: 1,
            clearance: 0,
        },
    )
}

fn initial_route(layout: &Layout) -> Route {
    let c = &layout.circles()[0];
    let a = layout.portals()[0];
    let b = layout.portals()[1];
    Route {
        circle: 0,
        cells: vec![
            a.grid_cell,
            a.transition_cell,
            c.sector(1, 0).expect("outer sector"),
            c.sector(0, 0).expect("inner sector"),
            c.center_cell(),
            c.sector(0, 1).expect("inner sector"),
            c.sector(1, 1).expect("outer sector"),
            b.transition_cell,
            b.grid_cell,
        ],
    }
}

fn make(mode: MotionMode, epoch: u64) -> Result<Scene, Error> {
    let layout = layout(mode)?;
    let route = initial_route(&layout);
    let start = route.cells[0];
    Scene::new(layout, &[route], &[start], 2, epoch, &mut Seeded(SEED))
}

fn run(mode: MotionMode) -> Result<(), Error> {
    println!("mode: {mode:?}, construction seed: {SEED:#x}");
    let mut scene = make(mode, 1)?;
    let mut work = MotionWorkspace::new(&scene)?;
    let route = scene.routes()[0].cells.clone();
    println!("  connected route: {:?}", route);
    let mut wall = 0;
    let mut i = 1;
    while i < route.len() {
        scene.begin_crossing(scene.stamp(), 0, route[i], 10)?;
        if i == 3 {
            let stamp = scene.stamp();
            assert_eq!(
                scene.advance_motion(stamp, &[128, 128], &mut work),
                Err(Error::Occupied)
            );
            assert_eq!(scene.stamp(), stamp);
            println!("  occupied inter-ring doorway rejected motion atomically");
            let patch = scene.begin_shatter(scene.stamp(), &[route[i]])?;
            assert_eq!(scene.patch_stage(patch)?, Stage::Draining);
            assert_eq!(scene.hide_patch(scene.stamp(), patch), Err(Error::Occupied));
            wall += 10;
            scene.tick(scene.stamp(), wall)?;
            assert_eq!(scene.walkers()[0].cell(), route[i]);
            scene.hide_patch(scene.stamp(), patch)?;
            scene.scatter_patch(scene.stamp(), patch, 5)?;
            wall += 5;
            scene.tick(scene.stamp(), wall)?;
            scene.reform_patch(scene.stamp(), patch, 5, Edit::default())?;
            wall += 5;
            scene.tick(scene.stamp(), wall)?;
            assert_eq!(scene.walkers()[0].state(), WalkerState::Ready);
            println!("  shatter drained -> target-local park -> hidden -> scattered -> reformed");
        } else {
            wall += 10;
            scene.tick(scene.stamp(), wall)?;
        }
        println!(
            "  {:?} at {:?}",
            scene.layout().cells()[route[i]],
            scene.walker_pose(0)?
        );
        i += 1;
    }
    assert_eq!(
        scene.walkers()[0].cell(),
        *route.last().expect("exterior endpoint")
    );
    println!("  grid -> polar interior -> different portal -> grid complete");
    let mut exchanges = 0;
    let mut elapsed = 0;
    while elapsed < TURN * 3 {
        let requested = 128.min(TURN * 3 - elapsed);
        let advance = scene.advance_motion(scene.stamp(), &[requested, requested], &mut work)?;
        elapsed += requested / advance.divisor as i32;
        exchanges += advance.event.replaced;
        if advance.event.replaced != 0 {
            println!(
                "  moving-doorway replacement: {} edges, divisor {}, revision {}",
                advance.event.replaced, advance.divisor, advance.event.stamp.revision
            );
        }
        if elapsed == 128 {
            let circle = &scene.layout().circles()[0];
            println!(
                "  inter-ring motion event: offsets {} / {}, {} moving tree doorways",
                circle.ring_offset(0, scene.phases())?,
                circle.ring_offset(1, scene.phases())?,
                advance.event.moving_doorways
            );
        }
    }
    if mode == MotionMode::Spinning {
        assert!(exchanges > 0, "spins must replace moving doorways");
    }
    assert_eq!(scene.phases(), &[0, 0]);
    println!("  three complete phase periods, {exchanges} replaced edges, no graph rebuilding");
    let old = scene.stamp();
    scene.tick(old, wall + 1)?;
    assert_eq!(scene.tick(old, wall + 2), Err(Error::StaleRevision));
    let first = scene.request_layout(scene.stamp())?;
    let latest = scene.request_layout(scene.stamp())?;
    assert_eq!(
        scene.publish_layout(first, make(mode, first)?),
        Err(Error::StaleEpoch)
    );
    let retired = scene.publish_layout(latest, make(mode, latest)?)?;
    assert_eq!(
        scene.tick(
            Stamp {
                epoch: old.epoch,
                revision: 0
            },
            wall + 2
        ),
        Err(Error::StaleEpoch)
    );
    println!("  superseded epoch rejected; retired {retired:?}");
    Ok(())
}

fn main() -> Result<(), Error> {
    let source = layout(MotionMode::Spinning)?;
    let mut invalid = initial_route(&source);
    invalid.cells[4] = invalid.cells[2];
    assert!(Scene::new(source, &[invalid], &[], 0, 1, &mut Seeded(SEED)).is_err());
    assert!(Layout::new(
        GridSpec {
            columns: 0,
            rows: 1,
            origin: Point { x: 0, y: 0 },
            cell_size: 10
        },
        vec![],
        &[],
        Geometry {
            viewport: Rect {
                min: Point { x: 0, y: 0 },
                max: Point { x: 100, y: 100 }
            },
            obstacles: vec![],
            walker_radius: 1,
            clearance: 0
        }
    )
    .is_err());
    println!("cyclic route and invalid layout rejected");
    run(MotionMode::Spinning)?;
    run(MotionMode::Twisting {
        amplitude: 32,
        max_relative: 64,
    })
}
