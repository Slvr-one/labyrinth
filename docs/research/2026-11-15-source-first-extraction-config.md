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

The diagnostic Aeneas run failed to join motion contexts and produced no Lean output. The two source helper refactors address only those observed joins; they do not establish complete translation. Full unrestricted extraction may still stop on missing `Vec::clear`, `Option<T>::Debug`, or another demonstrated model dependency. If the generated full-scene functions do not compile, record this obligation as **blocked on the exact missing generated model/body**. Do not substitute an abstract-only capacity theorem, a hand-written stand-in scene function, narrowed roots, opaque bodies, or a completion claim.
