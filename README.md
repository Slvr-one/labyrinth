# Labyrinth

A planned Rust/Wasm maze library with Lean 4 verification, licensed under Apache-2.0.

## Status

Phase 1 has a checked Rust-to-Lean feasibility operation and an incorrect-update rejection gate.
The full maze library, structural/solver proofs and Wasm package are not complete; the website
effect remains JavaScript.

- [Exact proof coverage, trust assumptions and reproduction](docs/properties.md)
- [Pinned toolchain revisions](toolchain-pins.json)

## Research

- [Algorithm and verification research — 2026-11-06](docs/research/2026-11-06-algorithm-and-verification.md)
  records the source behavior, toolchain prerequisites, sampled checks, metric-definition
  gaps, and design requirements.
