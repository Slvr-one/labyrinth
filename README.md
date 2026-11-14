# Labyrinth

A Rust maze core with connected grid/polar topology; Lean verification and Wasm delivery are in progress. Licensed under Apache-2.0.

## Status

Phase 1 is manually accepted. Phase 2 has a native connected-scene implementation, production
boundary-event planning, and handwritten structural proofs in progress. Native scenarios pass;
the complete extraction/proof gate does not. This is not a verified library milestone.
Solver/metric proofs, Wasm parity and Portfolio integration remain later gates; the website
still uses its existing JavaScript.

- [Exact proof coverage, trust assumptions and reproduction](docs/properties.md)
- [Pinned toolchain revisions](toolchain-pins.json)

## Research and planning

- [Algorithm and verification research — 2026-11-06](docs/research/2026-11-06-algorithm-and-verification.md)
  records the source behavior, toolchain prerequisites, sampled checks, and metric-definition
  gaps. Research and the detailed plan are reviewed.
- [Approved implementation plan — phase 2 in progress](docs/plans/2026-11-06-labyrinth-library-and-ui.md)
  retains the full proof/metric scope, configurable ring modes, and connected grid-to-circle
  walker traversal through final browser acceptance.
- [Planning track](https://github.com/NavadaAI/Atlas/pull/317)
  retains the original decisions and points to the canonical library documents; access is required.

The owner accepted phase 1 and authorized phase 2 on 2026-11-14. Phase-2 manual acceptance,
merging and deployment remain separate gates.

## Native trace

With the pinned isolated toolchain configured as described in the proof-coverage document:

```sh
cd rust
cargo test
cargo run --example phase2_trace
```

The example uses a recorded construction seed, traverses the actual polar interior between
different portals, and exercises both motion modes through the production planner.
`Scene::advance_motion` chooses safe sparse replacements; `Scene::motion` validates an explicit
caller-proposed update. `MotionAdvance::divisor` reports a consumed subinterval when a request
crosses more than one doorway event.
