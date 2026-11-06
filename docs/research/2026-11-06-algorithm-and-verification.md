---
date: 2026-11-06T17:13:55Z
repository: Slvr-one/labyrinth
git_commit: e12b7c61586fec44afb8024785347e56659dfe1d
branch: research/labyrinth-verification
topic: Existing maze algorithm and Rust-to-Lean verification prerequisites
status: reviewed-for-planning
tags: [research, maze, rust, lean, aeneas]
---

# Labyrinth algorithm and verification research

## Question and current state

What does the Portfolio maze actually implement, what can be reused for a standalone
Rust/Wasm library with Lean proofs, and which claims in the pending plan need correction?

At the researched library revision, only LICENSE exists. There is no Rust crate, Lean
package, proof, extraction pipeline, or Wasm artifact. The [existing plan](https://github.com/NavadaAI/Atlas/pull/317)
is open, not landed; this research does not approve that plan or implement it.

Scope recorded in that plan: a public Apache-2.0 library; Rust/Wasm; all listed structural,
dynamic, solvability, solver, and difficulty properties in the first milestone. Integrating
the library into Portfolio is a separate follow-on. No property is dropped by this research.

## Sources and evidence levels

- [Portfolio source](https://github.com/Slvr-one/portfolio/blob/b332b70a1df233ce4d3c5306f439f340a0b740d0/site/public/labyrinth.js)
  and [configuration](https://github.com/Slvr-one/portfolio/blob/b332b70a1df233ce4d3c5306f439f340a0b740d0/site/src/config.rs)
  are the implementation evidence. Portfolio is private; access is required for these links.
- [Plan revision under review](https://github.com/NavadaAI/Atlas/blob/4ac687ab16d4e7bd95e49d1da3f632a03b0e1355/Docs/projects/labyrinth/NAV-1063-labyrinth-lean4-plan.md)
  records intent, not implemented behavior. Access is required.
- Upstream code, toolchain pins, licenses, and registry metadata below are first-party
  documentation, not evidence that extraction works on this project.
- Local smoke results below are sampled execution, not universal proofs.
- Exa was unavailable. Research used first-party GitHub/raw pages, authenticated GitHub
  API reads, and crates.io metadata. No external toolchain was installed.

## Existing rectangular maze

The grid is a flat parent array indexed by `row * cols + col`. In the completed tree,
one root has parent `-1`; initialization additionally uses `-2` for undiscovered cells.
The renderer draws walls from undirected adjacency, not pointer direction. Its viewport
layout includes an extra row and column; the abstract tree includes masked/off-screen cells.

| Operation | Actual behavior | Conditions relevant to proofs |
|---|---|---|
| `initGrid`, lines 49–70 | Iterative randomized DFS, recording discovery parents | Positive dimensions, valid indices, connected rectangular grid; DFS does not sample spanning trees uniformly |
| `reroot`, lines 84–88 | Reverse parent pointers along the target-to-root path | Existing valid tree and in-range target; undirected edges are unchanged |
| `step`, line 82 | Write old root's parent, clear the new root's parent, update root | The target must be a distinct grid neighbor. It can exchange an edge or merely reverse its orientation |
| `advanceWalker`, lines 110–133 | Heading-biased neighbor choice, then `reroot(position)` and `step(neighbor)` | Neighbor policy uses floating-point trigonometry and a circle-occlusion mask; it is not a solver following passages |
| `shatter`, lines 237–272 | Select jagged patch, then perform `12 * hit.length` origin-shift steps | Not DFS regeneration; accepted operations preserve the tree under their adjacency conditions |
| Resize, lines 219–234 | Reinitialize when grid dimensions change | A new constructor run, not a re-root operation |

A root shift preserves a tree by reconnecting the component detached when the target's old
parent edge is removed. This describes the intended postcondition of a completed operation,
not a proof about every intermediate array write or arbitrary invalid arguments.

`randomNeighbour` (lines 72–80) prefers the supplied region but falls back to all neighboring
cells when no region neighbor exists. Patch regeneration is therefore not an unconditional
strict-locality guarantee. Walkers also fall back to masked cells when no unmasked neighbor
exists. A finite patch walk does not guarantee that every cell changes or that the resulting
maze differs from the old one.

The source has no entrance, exit, solver, or difficulty score. The initial DFS distribution
is not the distribution of a later snapshot after biased walkers and patch operations.

## Polar mazes and presentation state

`polarMaze` (lines 135–168) runs a separate DFS over ring/sector cells. It stores an
undirected link set rather than grid parent pointers. It then emits arcs/radials for drawing.
It does not dynamically rewire the polar graph.

Ring angles and alternating rotation directions are rendering state. Independently rotating
rings do not preserve alignment of the generated graph's passages. A theorem about that
abstract polar graph must not be presented as a theorem about navigability of the rotated
picture.

Colors, glow, trail drawing, content fading, displacement, and ring angles are presentation.
Some presentation-derived inputs still influence accepted mutations: the circle mask affects
walker selection; break deadlines and patch rectangles gate subsequent clicks. The extraction
contract must distinguish these inputs from maze topology rather than calling all current
browser state independent.

## Corrections required in the existing plan

| Current claim | Correction supported by source |
|---|---|
| Uniformly random spanning tree, with DFS bias | A randomized DFS discovery tree; no uniform-spanning-tree claim |
| Re-root by flipping one parent pointer | Separate path reversal (`reroot`) from two-parent-write origin shift (`step`) |
| Shattered patch regenerated with DFS | Bounded region-preferred origin shifts, including neighbor fallback behavior |
| Invariant maintained throughout without conditions | Specify valid grids/indices, operation preconditions, completed-operation states, and initialization/resize |
| Lean theorems directly apply to matching Rust types | State and establish representation correspondence for translated Rust functions |
| Aeneas is Lean-to-Rust | Rust → MIR → Charon LLBC → Aeneas functional Lean definitions → handwritten proofs |
| Mathlib supplies the DFS correctness proof | Mathlib supplies graph/tree predicates and structural/existence theorems, not this constructor's correctness |
| Repository already has the proposed Lean/Rust layout | It did not at the researched revision; layout remains proposed |
| Solve rate and difficulty already identify proof targets | Solver, snapshot semantics, endpoints, budget, normalization, and weights are not defined |

## Rust-to-Lean tooling

[Aeneas](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/README.md)
translates a subset of safe Rust through Charon into a functional model. The generated
[Lean tutorial](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/tests/lean/Tutorial/Tutorial.lean)
is distinct from its [handwritten proofs](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/tests/lean/Tutorial/Solutions.lean).
It neither generates Rust from an independent Lean model nor automatically proves maze properties.

| Component | Retrieved compatible revision/version |
|---|---|
| Aeneas | `87cfe2f5d663afd0a1fba154d41178f7a4420bb2` |
| Charon | `8cae8fd1905946de61147a65ecdd7122cc6b491b` |
| Charon Rust compiler | `nightly-2026-09-17` |
| Lean | `leanprover/lean4:v4.35.0` |
| Aeneas mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

Sources: [Charon pin](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/charon-pin),
[compiler/toolchain](https://github.com/AeneasVerif/charon/blob/8cae8fd1905946de61147a65ecdd7122cc6b491b/charon/rust-toolchain),
[Lean toolchain](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/backends/lean/lean-toolchain),
[mathlib manifest](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/backends/lean/lake-manifest.json).

The [Vec model](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/backends/lean/Aeneas/Std/Alloc/Vec.lean)
and [Rust tutorial](https://github.com/AeneasVerif/aeneas/blob/87cfe2f5d663afd0a1fba154d41178f7a4420bb2/tests/src/tutorial/src/lib.rs)
provide concrete evidence for vector contents, mutable indexing, and ordinary loops. Bounds,
arithmetic, failure, and termination obligations remain. Not every collection method or
control-flow shape is supported; nested-loop exits and mutable-reference generic instantiation
have documented limitations. Floating-point walker compatibility has not been established.

The documented workflow builds matching Charon/Aeneas, runs `charon cargo --preset=aeneas`
in a Rust crate, translates its LLBC with Aeneas's Lean backend, and checks handwritten
specifications in a compatible Lake package. A working example must precede a project-level
compatibility claim. The installed stable Rust is not the pinned extraction compiler.

Lean checking a translated model does not by itself certify translation implementation,
LLVM/Wasm compilation, JavaScript bindings, shipped-source identity, allocation failure,
or runtime performance. Target-width assumptions also matter for Rust `usize` on Wasm.

## Reusable graph and maze work

| Source | What exists | What it does not supply |
|---|---|---|
| [Pinned mathlib Acyclic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean) | `IsTree.existsUnique_path`, spanning-forest/tree existence and extension; Apache-2.0 | Correctness of this DFS parent array, root shifts, patches, randomness, or metrics |
| [lean4-maze](https://github.com/dwrensha/lean4-maze/tree/fb7e61cb1a224ead7eac95de1511620861cd44fe) | Movement and escape predicates, educational tactics; Apache-2.0 | Verified maze generation or dynamic-tree preservation; its Lean v4.22.0-rc2 pin differs |
| [amaze](https://github.com/sunsided/amaze-rs/tree/06c00622b6293fe199407677896533eb9e9c0760) | Generators, solvers, structural statistics; published 0.4.1; EUPL-1.2 OR MIT OR Apache-2.0 | Dependency-free/no_std or proof-carrying replacement; uses std and mandatory rand |
| [knossos](https://github.com/unrenamed/knossos/tree/91c4618bb1c244d67c4d4a913e72f91c65b9c5de) | Generation algorithms, seeding, rendering/export; published 1.2.0; Apache-2.0 | Dependency-free core; mandatory rand/image/clap/bitflags, recursive DFS |

Mathlib [spanning-forest work](https://github.com/leanprover-community/mathlib4/pull/33118)
was integrated through Bors even though GitHub's PR merge fields are misleading. The pinned
source has the declarations. Its current existence proof uses maximal acyclic extension,
not execution of a randomized DFS constructor. Unique-path results can be reused after
establishing that the concrete representation induces an `IsTree` graph.

The existing maze crates are useful references, not evidence that the full requested
proof suite can be imported. In particular, amaze counts degree-zero or degree-one cells
as dead ends, whereas the pending plan asks for degree exactly one.

## Executed checks

- Live browser: opened Background, exercised shatter/rebuild. A sampled canvas region's
  aggregate alpha went from 72161 to 0, then 28584 after rebuilding. This proves observed
  disappearance/reappearance, not a graph invariant.
- Live reduced motion: canvas image unchanged across the 600ms observation interval.
- Narrow 390px layout: document width remained 390px; no captured page errors. Touch-specific
  selection was not verified: the browser still reported a fine pointer.
- In-memory harness of the shipped JS functions, with deterministic random input:
  `1×2`, `2×1`, `4×4`, and `30×20` grids each passed tree checks after construction,
  re-rooting, 250 walker steps, and six shatters. Checks covered one root, in-bounds adjacent
  parents, no parent cycles, reachability to root, and unchanged undirected edges on re-root.
- The same harness observed a `1×1` walker TypeError at `cand[0][0]`. This is a reusable-library
  boundary case, not evidence that an ordinary visible browser viewport currently hits it.
- A region predicate allowing only the current cell caused `randomNeighbour` to return an
  outside neighbor, confirming the documented fallback.
- Refreshed Portfolio Markdown: all 13 local link targets exist; the configuration heading
  and cursor defaults match the referenced README/source.

No Rust library tests, Lean builds, translation, theorem checks, Wasm build, or end-to-end
proof were run. The environment lacks Lean/Lake/Elan, Charon/Aeneas, OPAM, and wasm-pack;
Rust 1.98.1 and Cargo are present. No `hack/spec_metadata.sh` exists in these repos and
labyrinth is not mapped to HumanLayer thoughts; metadata above was gathered directly.

## Questions for the research/plan gate

1. Are solve-rate and difficulty properties about a frozen abstract maze, or about a solver
   racing ongoing rewiring? The current source specifies neither. Start/exit, policy,
   budget, and probability model must be explicit.
2. How is the composite score normalized and weighted? There is no existing score or
   evidence establishing correspondence to human difficulty. Intellectuality currently
   means junction count on a chosen path, not a validated cognitive measure.
3. The required no_std core still needs an allocation/randomness contract for runtime-sized
   grids; `no_std + alloc` and dependency-free do not mean allocation-free.
4. The Aeneas subset must be exercised on the actual representation and operations before
   selecting it as the demonstrated correspondence mechanism. All required properties stay
   in scope; lack of local feasibility evidence is not permission to replace them with tests.

## Owner review — 2026-11-06

- Research accepted for a corrected implementation plan; implementation remains unapproved.
- Solver analysis must cover both frozen and evolving mazes.
- Overall delivery includes validation through the Portfolio UI, not just library/proof builds.
  The reported inability of walkers to enter circular mazes is an acceptance failure.
  Plan genuine grid-to-polar passage connectivity and traversal; do not simulate crossings
  by drawing walkers over walls.
- Portfolio integration remains a distinct phase/PR, but stays within the overseen delivery
  through browser acceptance. The earlier separate-follow-on decision is not a stopping point.
- Documentation commits and PRs are authorized. Merging and deployment remain separate gates.
- The five-phase order was approved. Both spinning-doorway and bounded-twisting ring modes
  must be configurable, alongside behavior tunables; valid passage/collision rules remain
  enforced constraints.
- The [canonical implementation plan](../plans/2026-11-06-labyrinth-library-and-ui.md)
  replaces the earlier proposal as the detailed design, pending explicit implementation approval.
