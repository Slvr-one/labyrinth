# Phase 1: actual Rust-to-Lean correspondence

## Scope

The feasibility operation uses borrowed parent storage and performs an indexed update after
an indexed, bounded parent-chain walk. Root entries point to themselves. The crate is
`no_std`, has no runtime dependencies, and neither allocates nor copies parent storage.
It is not the full maze library, and the Portfolio still uses its existing JavaScript.

| Rust operation | Extracted Lean | Checked statement |
|---|---|---|
| `tree::set_parent` | `labyrinth_core.tree.set_parent` | `set_parent_spec`: every application-level success updates exactly the requested index; both requested indices are in range; every application-level error preserves the original storage |
| `tree::reaches` | `labyrinth_core.tree.reaches` and its extracted loop | Translation feasibility only; loop totality and semantic correctness are not proved in phase 1 |
| `tree::random_reparent<R: Rng>` | `labyrinth_core.tree.random_reparent` and `tree.Rng` | Translation feasibility and native boundary scenarios; no probability or uniformity theorem |

The theorem quantifies over the actual extracted `set_parent`, including its call to the
extracted loop. It assumes that evaluation returns an application result. It does **not**
prove termination, panic freedom, acyclicity, root uniqueness, or tree preservation.
Those structural obligations remain in the approved phase-2 gate; the solver/metric suite
remains in phase 3. No independent Lean implementation substitutes for the Rust operation.

Existing parent entries must be valid indices. Malformed storage can panic in the walk;
this feasibility API is not a validated carrier constructor. Out-of-range requested IDs,
self-parent requests, and detected cycles return explicit errors without mutation.
A singleton self-parent request is rejected; this is not yet the stationary-walker API.

## Reproduce

Use the revisions in [`toolchain-pins.json`](../toolchain-pins.json) and the dependency lock
[`lean/lake-manifest.json`](../lean/lake-manifest.json). Upstream build prerequisites and
source references are recorded in the [reviewed research](research/2026-11-06-algorithm-and-verification.md#rust-to-lean-tooling).

Set `LABYRINTH_TOOLCHAINS` to an isolated installation directory with this layout:

```text
bin/charon, bin/charon-driver, bin/aeneas
src/charon/                 matching pinned Charon source
src/aeneas/                 matching pinned Aeneas source
cargo/, rustup/             isolated Cargo/Rustup homes
elan/                      isolated Elan home, including bin/lean and bin/lake
```

The Rust and Lean toolchain files select their pinned compilers. Do not change the machine's
default compiler. Install `rustfmt` and `clippy` in the isolated extraction toolchain for
native checks. Populate the pinned Lake dependencies once with `lake update` from `lean/`
using that isolated environment; dependencies may require upstream Mathlib build/cache setup.
The check runner assumes these tools/dependencies are available; it does not install them.

From the repository root:

```sh
python3 scripts/check-phase1.py
```

The runner checks the translator source revisions and Aeneas executable version, invokes
Charon on the actual crate, regenerates the Lean definitions, runs `lake build` with Lean
warnings treated as errors, and prints the theorem's imported axioms. It then copies the
Rust source into a temporary directory, changes the indexed assignment to store `child`
instead of `new_parent`, and independently extracts and compiles that incorrect operation.
The unchanged specification must report an unsolved proof goal. A compiler/translation
failure is not accepted as evidence that the specification rejects the mutation.
The temporary check reuses compiled dependencies without rebuilding their shared package caches.

For the native checks, use the same isolated Cargo/Rustup environment and run from `rust/`:

```sh
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo doc --no-deps
```

The native scenarios cover an exact successful update, singleton rejection, invalid requested
indices with unchanged storage, cycle rejection, and the injected integer-choice adapter.
They are executions, not universal proofs.

## Trust and limitations

The checked theorem imports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No application axiom, `sorry`, `admit`, native-evaluation axiom, or skipped proof obligation
is used for this theorem. `lean/Audit.lean` prints the transitive axiom inventory.

Trusted components include the pinned Rust compiler/MIR, Charon extraction, Aeneas translation
and standard-library models, imported Lean/Mathlib infrastructure, and the Lean kernel.
The Lean theorem checks the generated functional model; it does not independently certify
those translators, native machine code, LLVM, Wasm compilation, browser bindings, or allocation
failure. Source-revision/version checks are not a reproducible-build attestation of tool binaries.

The executed native target is `aarch64-apple-darwin`, with 64-bit `usize`. The generated model
uses Aeneas `Usize`; this is not evidence of 32-bit Wasm parity. Width-sensitive arithmetic
and native/Wasm equivalence remain phase-4 acceptance criteria. Floating-point geometry,
DFS, portals, moving doorways, solver probabilities and difficulty metrics are not implemented
or verified by this feasibility operation.

The phase-1 manual gate is to inspect [`tree.rs`](../rust/src/tree.rs), its generated
[`Funs.lean`](../lean/LabyrinthCore/Funs.lean), and
[`set_parent_spec`](../lean/LabyrinthCore/Spec.lean) together. Phase 2 requires owner acceptance
of that gate. Merge and deployment require separate authorization.
