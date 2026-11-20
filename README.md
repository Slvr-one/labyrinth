# Labyrinth

A Rust maze core with connected grid/polar topology; Lean verification and Wasm delivery are in progress. Licensed under Apache-2.0.

## Status

Phase 1 has a checked Rust-to-Lean feasibility operation. Phase 2 has a native connected-scene
implementation, production boundary-event planning, and handwritten structural proofs in
progress. Native scenarios pass; the complete extraction/proof gate does not. This is not a
verified library milestone. Solver/metric proofs, Wasm parity and Portfolio integration remain
later phases; the website still uses its existing JavaScript.

- [Exact proof coverage, trust assumptions and reproduction](docs/properties.md)
- [Pinned toolchain revisions](toolchain-pins.json)

## Research

- [Algorithm and verification research — 2026-11-06](docs/research/2026-11-06-algorithm-and-verification.md)
  records the source behavior, toolchain prerequisites, sampled checks, metric-definition
  gaps, and design requirements.

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
