# Labyrinth

A planned Rust/Wasm maze library with Lean 4 verification, licensed under Apache-2.0.

## Status

Phase 1 has a checked Rust-to-Lean feasibility operation and an incorrect-update rejection gate.
Its manual acceptance is pending. The full maze library, structural/solver proofs and Wasm package
are not complete; the website effect remains JavaScript.

- [Exact proof coverage, trust assumptions and reproduction](docs/properties.md)
- [Pinned toolchain revisions](toolchain-pins.json)

## Research and planning

- [Algorithm and verification research — 2026-11-06](docs/research/2026-11-06-algorithm-and-verification.md)
  records the source behavior, toolchain prerequisites, sampled checks, and metric-definition
  gaps. Research and the detailed plan are reviewed.
- [Approved implementation plan — phase-1 manual gate pending](docs/plans/2026-11-06-labyrinth-library-and-ui.md)
  retains the full proof/metric scope, configurable ring modes, and connected grid-to-circle
  walker traversal through final browser acceptance.
- [Planning track](https://github.com/NavadaAI/Atlas/pull/317)
  retains the original decisions and points to the canonical library documents; access is required.

The owner resumed phase 1 on 2026-11-14. Accept its manual gate before phase 2; merge and deployment remain separately gated.
