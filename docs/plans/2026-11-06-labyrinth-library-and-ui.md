# Labyrinth library, verification, and connected UI implementation plan

- **Date:** 2026-11-06
- **Status:** DRAFT FOR IMPLEMENTATION APPROVAL — no implementation authorized by this document
- **Research:** [reviewed algorithm and verification findings](../research/2026-11-06-algorithm-and-verification.md)
- **Tracking:** [formal model and extraction work](https://linear.app/navada/issue/NAV-1063/labyrinth-algorithm-formal-lean-4-model-and-rust-extraction-plan)

## Outcome and scope

Build the public Apache-2.0 Rust/Wasm library with Lean verification, then integrate it into
Portfolio and verify the actual user-visible behavior. A library build, independent math
model, or decorative animation does not complete this delivery.

Retain every property from the first library milestone: DFS construction, re-rooting,
robustness, solvability, solve rate/time, solution length, dead-end ratio, branching factor,
intellectuality, and composite difficulty. Include both frozen snapshots and evolving
mazes. The library milestone is incomplete until all these properties and their stated
implementation correspondence are checked.

Portfolio integration has a distinct phase and PR, but remains owned through UI acceptance.
Walkers must enter circular mazes, traverse their passages, and return to the grid. All
claimed crossings must exist in the topology and rendered geometry.

## Reviewed decisions

- Public `Slvr-one/labyrinth`; Apache-2.0; Rust/Wasm now, no C FFI in this change.
- Research was accepted for planning on 2026-11-06. The five-phase order below was approved.
- Both frozen and evolving maze analysis are required.
- Both ring-motion approaches are required and configurable: indefinitely spinning rigid
  rings with moving doorways, and bounded twisting with fixed connectivity.
- Motion, walker, layout, and interaction tunables remain configuration, not hidden constants.
- Oversee each phase with actual execution and carry validation through the Portfolio UI.
- Documentation commits/PRs are authorized. Implementation-plan approval, merging, and live
  deployment are separate gates.

## Existing state and corrections

The website uses JavaScript, not a reusable Rust/Wasm maze library. The reviewed library
base had LICENSE only; subsequent changes are documentation/research, not implementation.

The grid uses a parent array. Initialization is randomized DFS, not uniform spanning-tree
sampling. `reroot` reverses a target-to-root path without changing undirected passages.
`step` writes two parent entries and may exchange an edge. Patches use bounded origin-shift
walks, not DFS regeneration; their neighbor fallback can escape the selected region.

The circular maze is a separate graph, masked out of walker selection. Its independently
rotating drawing does not preserve alignment of its abstract passages. This is the cause
of the reported circle-entry acceptance failure, not an implementation to retain under a
new wrapper.

Sampled source probes passed tree checks on four grid shapes and exposed a single-cell
walker failure. Those results are not Lean proofs. The research records exact source
revisions, observations, and unverified claims.

Aeneas's direction is Rust → Charon LLBC → functional Lean definitions → handwritten proofs.
Matching independently written Lean/Rust types does not establish correspondence. Mathlib
provides tree/unique-path mathematics, not correctness of this DFS constructor.

## Architecture and contracts

### One navigable topology

Use a finite simple undirected carrier graph `H`, dense epoch-local cell IDs, and a rooted
parent array defining the current passage tree `T ⊆ H`. Separate the carrier graph of
physically possible crossings from the currently open tree passages.

- Rectangular cells inside a circular replacement region are removed, not hidden while
  remaining traversable underneath it.
- Polar center/ring/sector cells and explicit transition cells join the retained grid.
- Distinguish candidate portals in `H` from open portals in `T`. Every enabled circle must
  have at least two open usable portals whose unique `T` path between exterior endpoints
  crosses that circle's polar interior. Its complete swept corridor must be visible and clear,
  not routed through clipped/off-screen sectors or underneath text.
- Construct a required interior-route forest first, then extend it to the global tree.
  Constructors, walker carving, patch rewiring and moving-doorway commits preserve a checked
  route certificate for every circle. A replacement certificate is published atomically with
  its new topology; no intermediate disconnected or exterior-only substitute is observable.
- Internal tree primitives retain their general tree-preservation theorem. The UI publication
  layer rejects transitions that violate the stronger route/reservation certificate.
  Do not join complete grid/polar trees with two bridges without removing a cycle edge.
- Fixed carrier adjacency uses compact preallocated storage, such as CSR. Moving-doorway
  admissibility is explicit state; a fixed adjacency table must not silently change meaning.
- Geometry maps each carrier edge to a shared boundary, an open doorway interval, and
  in-cell approach paths with sufficient clearance for the walker footprint.

`Epoch` identifies a complete layout; `Revision` identifies a committed topology snapshot.
A transition records passage changes and walker moves between revisions. The renderer
never combines parents from one revision with doorways from another.

Keep the standalone unconstrained DFS constructor and the scene constructor explicit.
For a scene, validate the required route edges as an acyclic forest, contract its components,
run DFS on the connected quotient carrier, then expand the selected inter-component edges
together with the forest and orient the resulting tree. Prove this concrete constructor
produces a spanning tree containing every required route, rather than citing existence
of some extension. Reject an impossible/cyclic route forest before publication.

### Core and browser responsibilities

The dependency-free runtime core uses `no_std + alloc` for runtime-sized grids. Allocate
construction/analysis workspaces once, reuse them, and avoid per-step neighbor/trail heap
allocation. Reject impossible sizes and checked-arithmetic overflow before publication.

Rust owns topology construction, parent-tree mutation, accepted moves, solver/metric state,
and validation of topology updates. JS owns DOM measurement, geometry embedding, canvas
rendering, pointer interaction, and the paused simulation clock. Presentation-derived
masks and crossing reservations are explicit inputs to accepted transitions, not implicit
changes to connectivity.

Random-choice inputs are injected and range-checked. Structural proofs cover every legal
choice sequence. Probability theorems state conditional uniformity/independence assumptions;
a reproducible PRNG seed is not proof of those assumptions. Native deterministic and browser
choice adapters must exercise the same core operations. Translation support for the chosen
adapter form is checked in phase 1 before expanding the implementation.

A topology-mutating walker is distinct from a passage-following solver. A walker may open
an admissible edge by a valid tree transition, but the opening is committed and rendered
before it traverses. A solver never carves a passage just to legalize its selected move.

Core errors are observable and leave the last published state unchanged: invalid dimensions,
disconnected/asymmetric carrier input, invalid IDs/choices, illegal transitions, incompatible
epoch/revision, insufficient workspace, and arithmetic overflow. A valid singleton is
stationary; it must not request a nonexistent neighbor.

### Configurable motion and interactions

Preserve existing `LAB_*` variables and their documented valid behavior. Add typed configuration
for both ring modes and the new connection behavior. The Worker remains the browser setting
source; do not add an unrelated settings panel.

| Group | Configurable inputs |
|---|---|
| Existing layout | Enable, cell/touch-cell size, ring size, circle counts, text clearance, line opacity |
| Existing walkers | Desktop/touch count, step interval, trail length |
| Existing interaction | Cursor radius/trail/intensity, shatter radius/hold/rebuild timing |
| Ring motion | Mode `spinning` or `twisting`, speed, alternating-direction policy, twisting amplitude/rate |
| Connections | Requested portal count, doorway clearance, transition-band width |
| Motion presentation | Walker interpolation speed/radius, trail intensity, shatter displacement/reform glint |

Use named typed fields and documented Worker-variable mappings, not an open-ended plugin
registry. New defaults preserve the current look where compatible: spinning mode, existing
ring-speed multiplier, two portals per circle, and current walker/cursor/shatter settings.
Derive safe geometric minima from walker size and cell/ring dimensions. Invalid configuration
must not create disconnected passages or disable collision checks. Configuration changes
that affect IDs/adjacency create a validated new epoch rather than mutating live IDs in place.

New Worker mappings and initial defaults:

| Variable | Default |
|---|---|
| `LAB_RING_MODE` | `spinning` |
| `LAB_RING_DIRECTIONS` | `alternating` (`same` and `reverse` are also valid) |
| `LAB_TWIST_MAX_RAD` | `0.35` |
| `LAB_TWIST_PERIOD_MS` | `20000` |
| `LAB_RING_BASE_SPEED_RAD_S` | `0.015` |
| `LAB_RING_SPEED_JITTER_RAD_S` | `0.05` |
| `LAB_PORTALS_PER_CIRCLE` | `2` |
| `LAB_PORTAL_CLEARANCE_PX` | `2`, in addition to the walker footprint |
| `LAB_TRANSITION_BAND_PX` | `max(cell, ring)` when unset |
| `LAB_WALKER_MOVE_MS` | `60`, bounded by the configured step interval |
| `LAB_WALKER_RADIUS_PX` | `2` |
| `LAB_WALKER_TRAIL_ALPHA` | `0.5` |
| `LAB_SHATTER_DISPLACEMENT` | `1`, multiplying the existing displacement profile |
| `LAB_SHATTER_MS` | `420` |
| `LAB_REFORM_WAVE_MS` | `160` |
| `LAB_REFORM_FADE_MS` | `380` |
| `LAB_REFORM_GLINT_ALPHA` | `0.75` |
| `LAB_SCENE_FADE_MS` | `180`, only when motion is permitted |

Ring speed continues to use `LAB_RING_SPEED`; all other existing variables keep their names.
Number rings from one. With clockwise positive, `alternating` assigns odd rings `+1` and
even rings `-1`; `same` assigns `+1` throughout; `reverse` negates `alternating`.
Spinning angular speed is direction × `LAB_RING_SPEED` × a once-sampled rate in
`[LAB_RING_BASE_SPEED_RAD_S, base + LAB_RING_SPEED_JITTER_RAD_S)`.
Twisting uses direction × amplitude × sin(phase), with phase advancing by
`2π × LAB_RING_SPEED × dt / LAB_TWIST_PERIOD_MS`. Zero speed freezes the current phase;
motion holds consume no phase time and never catch up on release.

Retain step-opportunity jitter only as scheduling input. A walker accepts no new move until
its current interpolation/reservation completes, even when its next jittered opportunity was
earlier. Keep at most one pending opportunity per walker; no catch-up move queue.
Validate finite values, opacity/range bounds and geometric clearance as one configuration.
Requested portal counts must permit at least two usable connections when a circle is enabled.
Reject an unsafe effective layout rather than exposing a knob that allows wall crossings.

Implement and test both modes:

1. **Spinning:** rigid sectors rotate indefinitely. Shared doorways are computed from actual
   sector overlap, with a minimum usable interval. Before an occupied or tree doorway loses
   clearance, commit a valid replacement or hold the relevant motion until the crossing
   finishes. Maintain a connected admissible carrier and passage tree across every doorway
   event. No disconnected interval while waiting for two old holes to line up.
   Occupants use cell-local coordinates and ride the sector's transform, rather than staying
   screen-fixed while walls rotate. An inter-cell crossing reserves both endpoint approach
   corridors and the shared doorway; hold all implicated ring/adapter transforms for the
   entire swept footprint, complete interpolation in that held shared frame, then transfer
   ownership to target-local coordinates before releasing the hold. Prioritize completion
   of accepted crossings over admitting new ones; no new wall may sweep an occupied corridor.
2. **Twisting:** apply one shared orientation-preserving polar deformation to walls, doorways,
   and walkers. Inter-ring bands and the outer grid adapter interpolate the angular offset.
   Bound relative twist, then reverse/unwind before clearance is lost. This is configurable
   bounded motion, not a claim of visual parity with indefinite spins.

Reserve active crossings against closure or incompatible geometry changes. Clip/expire a
historical trail when its passage closes; otherwise a trail can cross a newly drawn wall.

### Shatter, epoch replacement, and suspension

Shatter first closes admission to the affected region and drains accepted crossings.
Park remaining occupants at valid cell-local poses; fade those occupants and affected trails
out before displaced wall fragments move. Fragments are non-traversable presentation, not
passage geometry. Parked occupants do not move or carve while hidden. Core topology and
the protected through-route remain valid despite temporary movement restrictions.

Commit the valid patch topology/geometry before reopening. Re-form the walls, then restore
occupant visibility and movement only at the shared patch deadline after clearance checks.
Clear stale affected trails. Hit-testing, admission and the patch's lifetime include grid,
polar and adapter cells. A new shatter cannot bypass active reservations or an unfinished patch.

Resize, orientation and geometry-affecting mode/config changes construct a replacement epoch
off-screen while the old scene freezes. With motion enabled, fade the old scene to zero,
terminate its walkers explicitly, release reservations, cancel its callbacks and trails, swap
the complete validated epoch, and fade new walkers in at valid initial poses. Do not report
old walkers as teleported into new cell IDs. If reduced motion is active, perform one coherent
static scene replacement without a fade. Reject every late callback carrying the old epoch.

Hidden-page suspension and runtime reduced motion freeze the current interpolation fraction,
geometry phases and simulation clock, retaining a valid crossing reservation and pose.
Reduced motion renders that coherent frame and disables moving shatter/glow. Restoring motion
resumes from the saved fraction/phase with one animation loop and no wall-time backlog.
Epoch replacement during suspension disposes of the old reservation with the old epoch.


## Solver and metric definitions

These definitions make the requested properties checkable; they do not claim that a score
has been calibrated to human cognition.

### Shared inputs and baseline

For an epoch with `n ≥ 1`, use valid start `s`, exit `e`, solver-opportunity budget `B`, a
policy, random choices, and an update schedule. Start/exit are independent of the parent
representation's root. The exit is absorbing; a zero budget succeeds exactly when `s = e`.

The required probability baseline is a uniform random walk over current **passage** neighbors,
matching the original plan's random solver. Return reached-exit/budget-exhausted/error,
first-hit tick, actual move count, and versioned trace. Unique-path reconstruction supplies
a deterministic oracle, not a substitute for random-solver analysis.

Finite legal traces may represent other policies. Exact probability claims for additional
policies require an explicit finite state/kernel including policy and scheduler memory;
there is no claim that every imaginable heuristic has a finite expected solve time.

### Frozen snapshots

Let `τ` be the first exit-hitting tick. Solve rate is `F_B = P(τ ≤ B)`, not exits per second.
For a fixed tree, use the exact Lean/reference recurrence:

```text
f_0(v) = 1 if v == exit else 0
f_(b+1)(exit) = 1
f_(b+1)(v) = average(f_b(u) for passage-neighbors u of v), v != exit
F_B = f_B(start)
```

Prove recurrence correctness, `[0,1]` bounds, budget monotonicity, impossibility before the
unique-path distance, the capped-time identity `E[min(τ,B)] = Σ_(t<B)(1-F_t)`, and almost-sure
escape on a finite frozen tree.

For the unique path `v_0=s,…,v_k=e`, let `a_i` be the component size on the `v_i` side after
removing its next path edge. Prove `E[τ] = Σ_(i<k)(2*a_i-1)` and `L ≤ E[τ] ≤ (n-1)^2`.
Both values are zero for coincident endpoints. Provide the elementary finite-budget lower
bound based on host degree and following a path in at most `n-1` opportunities.

Runtime returns exact structural counts and integer frozen expected hitting time, with
checked overflow. Runtime ensembles report trials, successes, the empirical success fraction,
and capped-tick sum; label them empirical. Prove the expectation relationship under the
stated independent-trial assumptions. Exact finite recurrences/enumeration are Lean/reference
oracles for small cases, not an exponentially expensive production enumerator or invented
confidence intervals.

### Evolving mazes

Each opportunity: check exit → commit the scheduled finite batch of legal topology updates
→ capture its revision → select and execute a passage move → record position/revision and
check exit. Updates cannot close an edge between selection and traversal.

For fixed finite schedules, use the corresponding time-indexed recurrence. Adaptive schedules
include the full finite joint state: topology, position, policy state, and scheduler state.
Prove trace legality, epoch validity, finite-horizon probability correctness/bounds, and
monotonic success for budgets extending the same prefix-consistent schedule.

Do not infer eventual escape from connected snapshots. Prove the negative fixture with
vertices `a,b,e`: alternate trees `a-b-e` and `b-a-e` before successive moves from `a`.
The no-wait solver is forced to alternate `a,b` without reaching `e`, although every snapshot
is connected. This fixture concerns a general carrier graph, not an impossible triangle in
a rectangular-only four-neighbor grid.

Prove the conditional positive result: after updates eventually stop, continued uniform
passage walking hits the exit almost surely. A known frozen interval also gives a finite-budget
lower bound. Do not silently assume stabilization or fairness for arbitrary schedules.

### Structural metrics and score

`P(s,e)` includes both endpoints, `L = |P|-1`, `d(v)` is passage degree, and `Δ` is the
fixed epoch carrier-degree cap.

| Metric | Definition and required bounds |
|---|---|
| Solution length | `0 ≤ L ≤ n-1`; zero iff endpoints coincide |
| Dead-end ratio | `D/n`, where `D` counts degree exactly one; singleton gives zero; at least two leaves for `n ≥ 2` |
| Branching factor | Average `d(v)-1` over vertices with `d(v) ≥ 2`; zero for an empty set; otherwise between 1 and `Δ-1` |
| Intellectuality | Count vertices on `P` with degree at least three, including junction endpoints; `0 ≤ J ≤ L+1`; for `n ≥ 2`, `J ≤ D-2` |
| Difficulty | Convex combination of the normalized components below; bounded in `[0,1]` and coordinate-monotone for fixed weights/normalizers |

Normalize as `L/(n-1)` (zero for singleton), `D/n`, branching divided by `Δ-1` (zero if
`Δ ≤ 1`), and `J/n`. Caller supplies nonnegative rational weights summing to one. No implicit
calibrated weights. Return raw counts, normalization inputs, weights, and score representation.
Represent exact metric ratios and caller weights as reduced `u128` numerator/denominator
pairs with a positive denominator. Cancel common factors before checked multiplication;
return an explicit overflow error when the exact result is not representable. The core
does not round the score. Decimal formatting belongs in the adapter. Prove correspondence
to mathematical rational arithmetic on successful results and preservation on errors.

Re-rooting preserves all structural metrics, score, and frozen solve probabilities. Edge
exchanges preserve bounds, not metric values or monotone difficulty. Evolving metrics are
snapshot-indexed; temporal paths are not promised to be unique.

Define the initial DFS distribution by its root/neighbor-choice policy. Prove its probabilities
sum to one and every supported outcome is a tree. Define each expected metric/solve rate by
a finite weighted sum; universal metric bounds also bound these expectations. Do not claim
unproved closed-form DFS statistics or reuse this distribution after biased mutations.
The scene constructor has its own explicitly labeled constrained-DFS distribution; do not
report it as the unconstrained DFS ensemble. Define its finite choice distribution separately.

## Phases and verification gates

Every phase records exact source revisions, executed commands, passed/failed/unverified
results, and prerequisites in the task's delivery record. A worker's completion message is
not acceptance evidence. Do not promote readiness on unrun checks. Owner review of manual
criteria follows each phase before the next dependent phase starts.

### Phase 1 — toolchain and actual correspondence feasibility

**Files:** pinned toolchain/manifest files; `rust/Cargo.toml`; minimal actual topology/tree
operations in `rust/src/`; `lean/lakefile.toml`, `lean-toolchain`, generated definitions and
handwritten correspondence checks; `docs/properties.md`.

Use the researched compatible Aeneas/Charon/Lean/mathlib revisions. Isolate installation;
do not replace the machine's default compiler or claim stable Rust is the extraction compiler.
Translate the actual safe-Rust parent storage, indexed mutation, loop, error path, and random
adapter form. Handwritten Lean statements target the extracted functions, not a parallel
look-alike implementation.

**Automated acceptance:**
- [ ] Matching Charon emits LLBC; pinned Aeneas emits Lean; `lake build` checks the actual
  representative operation and correspondence proof.
- [ ] A deliberately incorrect parent update fails its specification; no `sorry`, `admit`,
  skipped obligation, or application-defined axiom substitutes for a required proof.
- [ ] Native singleton and invalid-index scenarios exercise the same Rust operation.
- [ ] Record imported axioms, supported subset limitations, target-width assumptions and
  trusted compiler/translator components.

**Manual acceptance:** owner can inspect a concrete Rust function, its generated Lean,
and checked theorem together. A failed feasibility gate stops dependent implementation;
it is not permission to silently switch to unconnected abstract proofs or tests-only claims.

### Phase 2 — unified topology, transitions, and structural proofs

**Files:** `rust/src/grid.rs`, `polar.rs`, `topology.rs`, `spanning_tree.rs`, `walker.rs`,
`shatter.rs`; consumer-behavior tests; matching Lean definitions/proofs for graph representation,
DFS, reroot, step, operation traces, and portal-transition constraints.

Build the combined carrier and global tree, both configurable ring modes, crossing reservations,
and strict epoch/revision publication. Factor visual fragmentation from topology mutation.
The safety contract is independent of RNG quality and applies to every accepted transition.

**Automated acceptance:**
- [ ] Constructors reject invalid/asymmetric/disconnected carriers and preserve singleton behavior.
- [ ] Prove DFS termination/tree construction, re-root edge-set preservation, edge-exchange
  preservation, and validity of every prefix of a finite accepted operation trace.
- [ ] Prove the contracted-forest scene constructor produces a global tree containing every
  required interior route; reject a cyclic forest or an impossible visible portal layout.
- [ ] Native seeded scenarios enter polar cells and exit by another portal; invalid or occupied
  doorway changes fail without publishing a partial state.
- [ ] Both motion modes retain connected admissible doorways across sector-boundary events.
- [ ] No per-step neighbor allocation or whole-graph rebuild/copy in a render tick.

**Manual acceptance:** inspect source-to-theorem mapping and native transition traces; all
required circular regions are connected, not decorative overlays. This does not yet satisfy
browser acceptance.

### Phase 3 — solvers, metrics, and the full first-milestone proof suite

**Files:** `rust/src/solver.rs`, `metrics.rs`; Lean `Solver`, `SolveRate`, `Properties`, and
correspondence files; `docs/properties.md` theorem-to-function/assumption table.

Implement the definitions above. The table maps every requested property to its runtime
observable, exact theorem, extracted function, and checked assumptions. Include frozen and
evolving semantics and both positive and negative temporal results.

**Automated acceptance:**
- [ ] All named structural, dynamic, solver, statistical and difficulty obligations check in Lean.
- [ ] Singleton: no neighbor request; success at zero; structural components zero.
- [ ] Two-cell path: `F_0=0`, `F_1=1`, expected ticks 1.
- [ ] Three-cell path endpoint-to-endpoint: distance 2, dead ends `2/3`, branching 1,
  `F_2=1/2`, expected ticks 4.
- [ ] Four-cell star leaf-to-leaf: distance 2, dead ends `3/4`, branching 2,
  intellectuality 1, expected ticks 6.
- [ ] Exact small evolving-schedule recurrence agrees with weighted enumeration; the alternating
  connected-tree fixture refutes unconditional eventual escape.
- [ ] Illegal choices, overflow and epoch mismatches return documented errors; re-root preserves
  metrics; accepted edge changes preserve their bounds.
- [ ] Full native Rust checks and `lake build` pass with no omitted first-milestone property.

**Manual acceptance:** review raw metrics/score weights and the complete correspondence table.
Do not label the library milestone complete if a property remains only a sketch or assumption.

### Phase 4 — Wasm parity and binding costs

**Files:** thin Wasm interface, versioned export contract, native/Wasm conformance fixtures,
minimal real rendering consumer, same-origin loading/build instructions.

Keep browser-specific dependencies outside the core. Export transition/snapshot data needed
for drawing; reuse typed memory views and bounded change buffers. Invalidate/reacquire views
after Wasm memory growth. Avoid whole-parent-array copies each frame.

**Automated acceptance:**
- [ ] Build the actual Wasm target and execute it; native and Wasm agree on seeded topology,
  mutations, solver results, metrics and errors.
- [ ] Test width-sensitive sizes/arithmetic and buffer ownership/version behavior.
- [ ] Exercise both ring modes through the real Wasm interface and a canvas consumer.
- [ ] Measure initialization, per-transition allocations and binding traffic; record actual
  artifact sizes and costs rather than asserting unmeasured superiority.

**Manual acceptance:** inspect an executing Wasm consumer and matching native trace. This is
not a deploy or a substitute for Portfolio integration.

### Phase 5 — Portfolio integration and actual UI acceptance

**Files:** Portfolio `site/public/labyrinth.js`, build/assets loading, `site/src/config.rs`,
background descriptions, CSP only if required, configuration/operations docs; consumer regression
coverage for the reported disconnected-circle behavior.

Replace duplicated JS maze logic with the approved versioned library. Keep canvas geometry,
DOM measurement and presentation in JS. Preserve content-first styling and existing working
interactions. Missing/failed Wasm leaves usable HTML and an inert decoration; never silently
fall back to the disconnected implementation.

**Automated/runtime acceptance:**
- [ ] Run the actual Portfolio build and serve its real assets/Worker locally with the actual CSP.
- [ ] Validate a versioned trace through grid → outer portal → polar interior → inter-ring passage
  → a different outer portal → grid, in both configurable modes. Move openings before walkers,
  and check the entire swept footprint against contemporaneous walls/doorway clearance.
- [ ] Capture a synchronized browser recording showing that same real path; report no wall
  crossings over that observed trace, not universal correctness from a video.
- [ ] The required synchronized traversal recording comes from the normal autonomous walker
  policy in both modes, without an externally commanded route or a special circle-seeking
  test policy. A seeded replay may reproduce that same production policy; additional seeded
  scenarios do not replace autonomous evidence. If autonomous traversal cannot be obtained,
  the gate fails; do not fake it with teleportation, a JS route, or permanent test controls.
- [ ] Cover multiple walkers, portal-area shatter/reform, resize/orientation/DPR, content scrolling,
  tab/disclosure/font/layout changes, hidden-page resume, and reduced-motion changes mid-crossing.
- [ ] Test light/dark, actual coarse/touch input, scroll/cancel/multi-touch gestures, links/text
  selection, no horizontal overflow, and usable content/navigation with JavaScript disabled.
- [ ] Respect motion preferences; suspend on hidden pages; resume one loop without a catch-up burst.
- [ ] Assert the specified outcomes: no entry into broken cells, occupants hidden before
  fragments move, re-entry only after the shared deadline, no old-epoch callbacks/reservations
  after replacement, and exact pose/fraction continuity on suspension and resumption.
- [ ] Inject missing/failing Wasm fetch, compilation/CSP rejection, incompatible exports/version,
  and initialization failure. Content, navigation and CV remain usable; the decoration is inert
  with no surviving animation loop, disconnected fallback, or partially initialized listeners.
- [ ] Compare startup, frame-time distributions, long tasks, memory and binding traffic with a
  matched existing-site baseline. Record measured regressions and resolve them; no invented
  performance pass threshold or per-frame whole-graph reconstruction.
- [ ] Existing Portfolio test gate and new consumer-visible regression scenarios pass.

**Manual acceptance:** owner reviews both configurable motion modes and the visible entering,
interior traversal, and exit behavior. Production publication requires separate approval,
verified credentials, and a live smoke on the published revision. Local success is not live success.

## Execution and ownership

Use dedicated non-default worktrees/branches. One writer owns each checkout; coordinate core
interfaces before handing independent slices to workers. Run expensive integration gates once
under the lead. Keep validation/trace evidence attributable to exact revisions, not agent claims.

The standalone library carries its detailed plan/research. Atlas retains the existing track and
owner rulings with links to the canonical library documents, rather than a competing full plan.
Portfolio integration uses a separate ordered PR depending on the tested library revision.

Progress reports distinguish planned, source implemented, proof checked, built, locally integrated,
review-ready and live states. Report the next failing/unverified gate, not just completed tasks.
No board is required or implicitly authorized.

## Non-goals, migration, and rollback

No unrelated Portfolio redesign, solver-game UI, settings dashboard, repository cleanup,
C FFI, new cloud platform, or claims of calibrated human difficulty. No removal of required
proofs, either requested motion mode, evolving semantics, or UI acceptance.

The existing Portfolio implementation remains live until the replacement passes local gates
and publication is approved. Ship JS/Wasm/config as one matched revision. A failed decoration
must not prevent content/CV/navigation use. Rollback restores the prior matched application
revision; it must not mix old JS and new Wasm. Merge/deploy authority remains with the owner.

## References

- [Reviewed source/tooling research and pinned upstream references](../research/2026-11-06-algorithm-and-verification.md)
- [Original planning track and recorded decisions](https://github.com/NavadaAI/Atlas/pull/317)
- [Portfolio implementation](https://github.com/Slvr-one/portfolio/blob/b332b70a1df233ce4d3c5306f439f340a0b740d0/site/public/labyrinth.js)
- [Portfolio configuration reference](https://github.com/Slvr-one/portfolio/blob/b332b70a1df233ce4d3c5306f439f340a0b740d0/README.md#background-configuration)
