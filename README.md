# Labyrinth

A Rust maze core with connected grid/polar topology, with Lean proofs about its extracted model; Wasm delivery is in progress. Licensed under Apache-2.0.

## Status

The crate implements connected grid/polar scenes with production boundary-event planning, and
the extraction/proof gate in `tools/check` passes. The proofs are about the extracted Lean model
of scene construction, edits, reservations, shatter, publication and the motion planner. Most are
partial correctness: they describe the results an operation returns, not that it returns. The
scene-wide invariant is proved for scenes reached from a successful `Scene::new` on a layout that
`Layout::new` accepted, through the listed operations. [docs/properties.md](docs/properties.md)
states exactly what is proved, under which hypotheses, the trusted components and what is not
proved. Solver/metric proofs, Wasm parity and Portfolio integration remain later phases; the
website still uses its existing JavaScript.

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

## Verification gate

The gate is a Rust program in `tools/check` (its own package, not part of `rust/`). With
`LABYRINTH_TOOLCHAINS` pointing at the isolated toolchains, from the repository root:

```sh
cargo run --release --manifest-path tools/check/Cargo.toml            # whole gate
cargo run --release --manifest-path tools/check/Cargo.toml -- --help  # checks and steps
```

Checks on the gate itself, from `tools/check`:

```sh
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test
```
