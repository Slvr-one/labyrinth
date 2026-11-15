# Verification coverage and reproduction

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

The runner checks translator source revisions and the Aeneas executable version, then extracts
the actual crate into temporary Lean files. They must byte-match the checked-in generated
definitions before `lake build` checks them with warnings treated as errors. Drift fails the
gate without overwriting the model that the owner inspects.

The theorem's imported axioms must be drawn only from `propext`, `Classical.choice`, and
`Quot.sound`; an unrecognized audit result also fails. A separate Lean fixture relying on an
application-defined axiom exercises this rejection.

The runner then copies the Rust source into a temporary directory, changes the indexed
assignment to store `child` instead of `new_parent`, and independently extracts and compiles
that incorrect operation. The unchanged specification must report an unsolved proof goal.
A compiler/translation failure is not accepted as evidence that the specification rejects
the mutation. Temporary checks reuse compiled dependencies without rebuilding shared caches.

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
[`set_parent_spec`](../lean/LabyrinthCore/Spec.lean) together. The owner accepted that gate
on 2026-11-14 with the limitations above and authorized phase 2. Phase-2 structural and
transition proofs are not established by this acceptance. Merge and deployment require
separate authorization.

## Phase 2 — native checkpoint, formal gate incomplete

The native crate now implements validated CSR carriers, ordinary DFS, required-forest
contraction/quotient DFS/expansion, sparse tree edits, combined grid/polar layouts, reservations,
shatter, suspension and epoch replacement. `Scene::advance_motion` performs production
boundary-event planning with reusable flow/search storage and sparse edge proposals; the
example no longer supplies a geometry-specific planner.

Spinning admission uses conservative radius/clearance bounds and checks the chosen exterior
portal pair over every quantized one-unit outer-ring sweep. Some geometrically feasible
layouts can be rejected by these conservative bounds. Accepted proposals still pass the
existing geometry, route, reservation and tree checks before publication. The returned
positive subdivision divisor specifies the consumed phase increments; errors never represent
a partially committed request.

Native tests cover multiple circles, unequal ring counts/sectors, impossible spinning layouts,
safe resized high-sector layouts, reserved crossings, stale workspaces and atomic rejection.
The seeded native example traverses grid → polar interior → different portal → grid in both
modes and completes three motion periods. Allocation instrumentation observed zero allocations
after initialization for the exercised crossings, ticks and production planning events.
These are execution results, not universal proofs or browser acceptance.

Several handwritten proof foundations check, including the parent representation's
interpretation as a connected acyclic graph and extracted validation/loop helpers. The extracted
`mutation_reroot_preserves` theorem establishes totality for valid carriers, trees and workspaces:
every undirected tree edge is preserved, errors leave the tree unchanged, and success occurs
exactly when the requested root is in bounds and path capacity is sufficient. Its axiom audit
contains only `propext`, `Classical.choice` and `Quot.sound`.

Both carrier constructors now have checked totality/soundness and valid-input acceptance
specifications. Generic DFS accepts bounded, root-reachable directed CSR, including parallel
arcs, under a total range-correct RNG contract. It proves all vertices discovered, a rooted
parent tree and exact incoming original-slot witnesses. The public `Tree::dfs` specification
returns `TreeValid` on valid carrier inputs with sufficient workspace and preserves RNG and
workspace on invalid-root or insufficient-capacity rejection. The twenty-five production roots
listed in `Audit.lean` use only the standard axioms above.

Checked helper composition now includes exact required-forest components, dense quotient
labels, degree counting, occupied-slot witnesses, quotient reachability, actual quotient DFS
acceptance, expanded selected-carrier acceptance and sparse batch attachment. Literal
orientation loops also prove all-cell reachability, exact parent/carrier edges, `TreeValid`
publication and workspace preservation. The current handwritten library builds strictly;
the outer constrained-constructor and scene-publication specifications remain unfinished.
The full source-extraction/correspondence gate remains incomplete.
The actual `edit_edges` theorem checks totality, error atomicity, workspace reuse,
root/length preservation, exact removed/added edge sets, carrier membership and successful
`TreeValid` preservation. Actual exchange and accepted finite trace-prefix preservation also
check: each recorded prefix remains valid, and individual errors leave publication unchanged.
Protected input tree edges disjoint from the actual removal list are preserved by successful
edits; this does not prove the separate scene guards establish that disjointness.
The checked-in generated core model does not currently cover the full scene/planner source.
The correspondence runner rejects model drift and unmodeled external-operation templates;
it must not be treated as a phase-2 pass until the complete source/model/proof gate succeeds.

No phase-2 manual acceptance, merge, Wasm result, browser result or deployment is claimed.
