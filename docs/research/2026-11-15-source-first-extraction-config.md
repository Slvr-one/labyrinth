# Source-first extraction configuration

## Scope

This recipe keeps the default whole-crate Charon roots and includes only audited standard-library bodies. It does not add `--start-from`, `--opaque`, `--exclude`, or `--extract-opaque-bodies`, and it does not change the extraction gate, Rust standard library, Aeneas models, or generated builtin registry.

The source changes retain `Vec::clear`, derived `Default`, public trait derives, both motion modes, and native error ordering. They do not replace unsupported operations with opaque declarations, abstract helpers, fresh vectors, or private `Option` state.

## Tested narrow Charon configuration

The bounded diagnostic used these exact Charon patterns:

```text
core::slice::{impl core::default::Default for &Slice<_>}::default
core::option::{impl core::default::Default for core::option::Option<_>}::default
core::result::_::is_err
```

The corresponding invocation shape was:

```sh
charon cargo --preset=aeneas --dest-file="$DEST" \
  '--include=core::slice::{impl core::default::Default for &Slice<_>}::default' \
  '--include=core::option::{impl core::default::Default for core::option::Option<_>}::default' \
  '--include=core::result::_::is_err'
```

Evidence: `../../../diagnostics/pure-std-llbc-20261115T200819911194Z/charon.log` and `result.json`. Whole-crate roots remained unrestricted, all three targeted methods had one transparent structured LLBC body, and the slice default additionally produced its promoted constant. The result establishes body availability only, not successful Aeneas translation or a proof.

The exact pinned Rust bodies are source-backed:

- shared-slice `Default`: `core/src/slice/mod.rs:5653-5657`, returning `&[]`;
- `Option<T>::default`: `core/src/option.rs:2303-2317`, returning `None`;
- `Result::is_err`: `core/src/result.rs:647-649`, delegating to `!self.is_ok()`; the pinned Aeneas model already maps `is_ok`.

## Further source-first candidates

Any further inclusion must be diagnosed one body at a time with the same unrestricted roots. The operation-specific generated name patterns and pinned sources below are candidates, not tested Charon CLI syntax and not approved model changes:

| Operation-specific generated pattern | Pinned Rust body | Required behavior inventory before inclusion |
|---|---|---|
| `core::option::{core::option::Option<&'0 @T>}::copied` | `core/src/option.rs:2135-2145` | `None`/`Some` identity after reference erasure; no clone call |
| `core::option::{core::clone::Clone<core::option::Option<@T>>}::clone` | `core/src/option.rs:2278-2283` | no payload call for `None`; one real payload clone for `Some` |
| `core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq` | `core/src/option.rs:2441-2450` | no comparison for mixed/`None`; one comparison for `Some`/`Some` |
| `core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains` | `core/src/ops/range.rs:539-544` | include only its `RangeBounds::contains` and bound dependencies; preserve exhausted ranges and comparator order |
| `core::num::{i32}::abs` | `core/src/num/int_macros.rs:3638-3647` | preserve the pinned profile's `i32::MIN` overflow behavior |
| `core::num::{i32}::rem_euclid` | `core/src/num/int_macros.rs:3258-3273` | preserve zero divisor, `MIN / -1`, negative-dividend, and divisor-`MIN` behavior |

These are taken from the Aeneas-generated missing-operation inventory. Before use, translate each generated pattern to Charon's Rust-pattern grammar, run an isolated body diagnostic, and record its exact dependency closure. Never broaden an include to `core::option`, `core::ops::range`, `core::num`, or another module.

`Vec::clear` is intentionally not a transparent-body candidate: its Rust body mutates raw allocation state and drops through pointers, while the pinned Lean `Vec` contains only a slice. Keep idiomatic `.clear()` in production source; a future content-level mapping and separate native allocation evidence require explicit owner approval. `Option<T>::Debug` likewise needs faithful branch/delegation through the existing formatter abstraction, not an unconditional-success shortcut.

## Carrier-edge budget equivalence

Let `E` be the validated carrier's canonical edge set and `R` the private `required` vector during one `check_routes` scan.

1. `Scene::new` reserves `required` with capacity at least `|E|`. The vector remains private, is never replaced or shrunk, and each scan starts with `required.clear()`, which preserves allocation.
2. Initially `R` is empty, so `NoDup(R)` and `R ⊆ E` hold.
3. Before an edge reaches the guard, `layout.doorway` has succeeded. Its first validation requires `carrier.contains_edge(edge)`, so the candidate is in `E`.
4. The push branch runs only when `!R.contains(edge)`. Therefore a pushed edge is new, preserving `NoDup(R)` and `R ⊆ E`.
5. For a newly admitted edge, `|R| < |E|`. Since native reserved capacity is at least `|E|`, both `|R| == |E|` and `|R| == capacity(R)` are false. Both versions therefore execute the same push, and that push cannot reallocate.
6. The guard remains after doorway validation and publication/tree validation. Consequently all earlier errors retain their order; on every reachable valid admission path, contents, result, first error, and allocation behavior are unchanged.

This is a program-scoped equivalence argument, not capacity reconstruction in Lean. The pinned slice-only `Vec` model cannot express allocator capacity.

## Remaining proof obligation and blocker rule

The required formal obligation is an induction over the actual generated full-scene `check_routes`/`check_route_edge` functions proving `NoDup(R)`, `R ⊆ E`, and equivalence of the logical carrier-edge guard to the former physical-capacity guard on every reachable publication path. That result must feed the generated scene constructor/publication correctness proofs and preserve the functions' actual error order.

The initial diagnostic failed motion-context joining. The narrow helpers and local enum binding below now allow unrestricted generation, but an eight-operation external template remains. The full-scene proof obligation is therefore **blocked on the exact missing generated model/body**, not complete. Do not substitute abstract-only capacity theorems, stand-in scene functions, narrowed roots or external axioms.

## Local enum scrutinee

`MotionWorkspace::plan_route` binds the copied `Cell` to `kind` before its sector match, following
the existing `eligible` pattern. This separates the indexed scene borrow from enum
expansion and the later mutable `route_through` call. The index expression is still
evaluated exactly once at the same loop position; sector filtering, route attempts,
first-error propagation and vector operations are unchanged. `Cell` is already `Copy`;
the binding introduces no clone or allocation.

The 2026-11-16 lead run completed unrestricted Charon/Aeneas generation with this binding.
It still emits an external template for signed abs/remainder, inclusive-range membership,
Option Debug/copied/clone/equality and Vec clear; zero-template acceptance fails.
Native fmt, strict Clippy, 53 tests, docs and both actual traversal traces passed.
The separate production-allocation instrument and full-scene Lean acceptance are not established.

## Full-source extraction invocation

Run from the checkout root. Set `LABYRINTH_TOOLCHAINS` to the existing pinned installation
and `OUT` to an absolute diagnostic directory outside the source tree:

```sh
: "${LABYRINTH_TOOLCHAINS:?set the pinned toolchain directory}"
: "${OUT:?set an absolute diagnostic output directory}"
export CARGO_HOME="$LABYRINTH_TOOLCHAINS/cargo"
export RUSTUP_HOME="$LABYRINTH_TOOLCHAINS/rustup"
export ELAN_HOME="$LABYRINTH_TOOLCHAINS/elan"
export PATH="$LABYRINTH_TOOLCHAINS/bin:$CARGO_HOME/bin:$ELAN_HOME/bin:$PATH"
mkdir -p "$OUT/lean"
export CARGO_TARGET_DIR="$OUT/cargo-target"
(
  cd rust
  charon cargo --preset=aeneas --dest-file="$OUT/labyrinth_core.llbc" \
    '--include=core::slice::{impl core::default::Default for &Slice<_>}::default' \
    '--include=core::option::{impl core::default::Default for core::option::Option<_>}::default' \
    '--include=core::result::_::is_err'
) >"$OUT/charon.log" 2>&1 &&
aeneas -backend lean -split-files -abort-on-error -warnings-as-errors \
  -no-progress-bar -dest "$OUT/lean" -subdir LabyrinthCore \
  "$OUT/labyrinth_core.llbc" >"$OUT/aeneas.log" 2>&1
```

Pins remain those in `toolchain-pins.json`: Charon
`8cae8fd1905946de61147a65ecdd7122cc6b491b`, Aeneas
`87cfe2f5d663afd0a1fba154d41178f7a4420bb2`, Rust `nightly-2026-09-17`
and Lean `v4.35.0`. The completed run retained unrestricted roots, all production modules
and the three diagnosed real bodies. Process exit zero does not satisfy the extraction
gate while an external template remains.

Only complete generation without `LabyrinthCore/FunsExternal_Template.lean` can
advance generated-scene proof integration. Preserve the complete generated output,
including pure-body dependencies, and reconcile `Types.lean`/`Funs.lean` and their
imports with the proof checkout before its strict Lean build and axiom audit.
`scripts/check-phase1.py` remains the unchanged phase-1 gate; its plain extraction
command does not apply these inclusion patterns and its checked-in-model comparison
is not evidence for the new full-scene output. Missing bodies or interpreter failures
remain blockers, not permission to narrow roots or introduce a model patch.
