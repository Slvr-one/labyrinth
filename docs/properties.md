# Verification coverage and reproduction

This page says exactly what is proved about the Rust crate, what is not, and how to reproduce the
check. Every statement below names a theorem in [`lean/LabyrinthCore`](../lean/LabyrinthCore) that is
a root of [`lean/Audit.lean`](../lean/Audit.lean), and gives its hypotheses and its kind.
All theorems are about the Lean model that Aeneas extracts from the Rust source, under the model
limits listed in "Trust and limitations". The Portfolio still uses its existing JavaScript.

## Summary

| Area | Status | Main theorems |
|---|---|---|
| Standard-library models | proved | `i32_abs_spec`, `i32_rem_euclid_spec`, `i32_div_spec`, `range_inclusive_contains_i32_spec`, `vec_clear_spec`, `option_eq_spec`, `slice_contains_spec` |
| Carriers, tree search, tree edits | proved (total) | `constructor_carrier_from_csr_spec`, `constructor_tree_dfs_spec`, `constructor_scene_dfs_spec`, `mutation_edit_edges_tree_valid`, `mutation_reroot_preserves` |
| `tree::set_parent` | proved as partial correctness | `set_parent_spec` |
| Route budget | proved as partial correctness | `scene_check_route_edge_budget`, `scene_check_routes_required_exact`, `scene_check_routes_ok_members` |
| Scene construction | proved as partial correctness | `scene_new_spec`, `scene_new_tree`, `scene_new_full_unconditional` |
| Edits (preflight, commit, motion, carve) | proved as partial correctness, except `scene_commit_edit_spec` (total) | `scene_preflight_edit_spec`, `scene_preflight_edit_accepted`, `scene_commit_edit_spec`, `scene_motion_spec`, `scene_carve_spec`, `prepare_motion_spec` |
| Epoch and revision publication | proved (total) | `check_stamp_spec`, `suspend_spec`, `resume_spec`, `request_layout_spec`, `publish_layout_spec`, `reject_layout_total`, `tick_spec` |
| Reservations | proved (total for admission and reservation lookup; partial correctness for crossings, removal and edit safety) | `admission_spec`, `reservation_spec`, `begin_crossing_outcome`, `check_removal_exact`, `preflight_edit_safe`, `motion_safe`, `carve_safe` |
| Shatter | proved (total for begin, hide, scatter; partial correctness for reform) | `begin_shatter_spec`, `hide_patch_spec`, `scatter_patch_spec`, `reform_patch_spec`, `reform_patch_headline`, `reform_patch_safe`, `tick_patch_progress` |
| Geometry totality | proved (total) | `layout_doorway_total`, `layout_new_total_closed`, `doorway_minimum_exact`, `grid_rect_touches_disk_total`, `from_edges_error_set` (partial correctness) |
| Scene invariant and reachability | proved as partial correctness | `sceneReachable_inv_unconditional`, `sceneReachableU_hold_exact`, `reachable_no_leaked_hold` |
| Motion planner (`advance_motion`) | proved as partial correctness for the scene invariant, safety, connectedness of the accepted result and workspace frames; **not proved**: that it always returns and always proposes an acceptable edit | `advance_motion_inv`, `advance_motion_safe`, `advance_motion_connected`, `sceneReachableM_inv`, `plan_ok_balanced` |

Section "Not proved" lists everything else that has no theorem.

## Two kinds of statement

- **Total.** The theorem says the extracted function always returns (no panic, no divergence) and the
  result satisfies the property. In Lean this is a `⦃ … ⦄` specification or an explicit
  `∃ r, f … = ok r ∧ …`.
- **Partial correctness.** The theorem says every result the function returns satisfies the property
  (`OkPost` in the sources). It says nothing about whether the function returns on every input. Most
  scene theorems are of this kind because they run through geometry code whose totality is proved
  separately and only under hypotheses (see "Geometry totality").

When a hypothesis is named below it is a hypothesis of the theorem itself; nothing is assumed beyond
what is listed.

## Standard-library models

The repo-owned [`FunsExternal.lean`](../lean/LabyrinthCore/FunsExternal.lean) defines the external
operations stock Aeneas leaves as templates. [`SceneStd.lean`](../lean/LabyrinthCore/SceneStd.lean)
gives step specifications for them and for the library operations the scene code uses. All are total
unless a hypothesis says otherwise:

- `i32_abs_spec`: the result is `|x|`; hypothesis `x` is not `i32::MIN`.
- `i32_rem_euclid_spec`: for a positive modulus the result equals `x % y`, lies in `[0, y)` and is
  congruent to `x` modulo `y`.
- `i32_div_spec`, `i32_div_turn_eight`, `i32_div_turn_four`: signed division truncates toward zero;
  hypotheses: divisor nonzero and not `MIN / -1`. The last two fix the two divisions of the turn
  constant that the arc code performs.
- `range_inclusive_contains_i32_spec`, `range_inclusive_contains_i32_new`: `RangeInclusive::contains`
  at `i32`.
- `option_copied`, `option_clone_i32`, `option_clone_u64`, `option_clone_usize`, `option_eq_spec`,
  `option_eq_i32_spec`, `option_eq_u64_spec`, `option_eq_usize_spec`: `Option` `copied`, `clone`
  and `==`.
- `vec_clear_spec`: `Vec::clear` returns the empty vector (content only; the model has no capacity).
- `option_debug_fmt_none`, `option_debug_fmt_some`: the two branches of `Option`'s `Debug::fmt`
  forward to the existing formatter operations.
- `slice_contains_spec` (hypothesis: the element equality is exact), `edge_eq_spec`,
  `slice_contains_edge_spec`: `Slice::contains` is list membership, also for edges.
- `option_ok_or_spec`, `option_ok_or_is_ok`, `result_is_err_spec`: `Option::ok_or` and
  `Result::is_err`.

The model limits that remain are in "Trust and limitations".

## Carriers, tree search and tree edits

The scene results build on these. All are total, with the hypotheses shown.

- Tree interpretation: `constructor_treeValid_isTree` (a `TreeValid` parent array is a tree as a graph)
  with its supporting lemmas `constructor_parentGraph_adj_iff`, `constructor_rooted_connected` and
  `constructor_rooted_isTree`.
- Carrier constructors: `constructor_carrier_from_csr_spec` and
  `constructor_carrier_from_edges_total_spec` (every returned carrier is `CarrierValid`; errors are
  unconstrained); `constructor_carrier_from_csr_accepts` and `constructor_carrier_from_edges_accepts`
  (valid input, with a storage-width hypothesis, is accepted).
- Tree search: `constructor_tree_dfs_spec` (for a valid carrier and workspace the result is a
  `TreeValid` tree rooted at the requested root with the workspace still valid, or `InvalidIndex`
  when the root is out of range, or `InsufficientWorkspace` when the workspace is too small; the RNG
  and workspace are returned unchanged on both errors; hypothesis: the RNG adapter is legal), with
  `constructor_tree_dfs_accepts`, `constructor_tree_dfs_invalid_root`,
  `constructor_tree_dfs_insufficient_workspace`, `constructor_depth_first_accepts` and
  `constructor_quotient_depth_first_accepts`.
- Required-forest tree search used by scene construction: `constructor_scene_dfs_spec` (the result
  is a `TreeValid` tree containing every required edge, or one of `InvalidIndex`,
  `InsufficientWorkspace`, `InvalidForest` (RNG and workspace unchanged) or `Overflow`),
  `constructor_scene_dfs_accepts` (acceptance under a valid forest, enough workspace and an
  allocation-size hypothesis), `constructor_scene_rejects_invalid_forest`,
  `constructor_scene_publish_accepts`, `constructor_scene_dfs_guarded`.
- Tree edits: `mutation_edit_edges_total_frame` and `mutation_edit_edges_tree_valid` (hypotheses:
  valid carrier, tree and workspace, path capacity at least the cell count, edge capacity at least the
  carrier's edge count; errors leave the tree unchanged; success keeps root and length, the new edge
  set is exactly the removed/added edit of the old one, every edge is a carrier edge, and the tree is
  valid); `mutation_edit_edges_preserves_disjoint` (protected tree edges disjoint from the removal
  list survive a successful edit); `mutation_exchange_tree_valid`, `mutation_operation_preserves`,
  `mutation_accepted_trace_prefix_valid` (every prefix of an accepted trace is valid).
- Re-rooting: `mutation_reroot_success` (for a valid tree and an in-range new root with enough path
  capacity the call succeeds, the result is valid and rooted there, and every undirected edge is
  preserved) and `mutation_reroot_preserves` (without those capacity hypotheses: errors leave the tree
  unchanged and success preserves validity and edges).

### `tree::set_parent`

`set_parent_spec` is partial correctness: whenever the extracted `tree::set_parent` returns, an
application-level success updates exactly the requested index with both indices in range, and every
application-level error leaves the storage unchanged. It does not prove termination or panic freedom
of `set_parent` or of the `tree::reaches` loop it calls, and it does not prove acyclicity.
Malformed storage can panic in the walk; this operation is not a validated carrier constructor.
The theorem is declared at the top level, outside the `Labyrinth` namespace, so its fully qualified
name is just `set_parent_spec` (it opens `labyrinth_core` but does not live in it).

## Route budget

Source: [`SceneRouteBudget.lean`](../lean/LabyrinthCore/SceneRouteBudget.lean). All three theorems are
partial correctness. They assume a valid carrier and that the scratch list of required edges
(`required`) is duplicate-free and contained in the carrier's edge list (`RouteInv`).

- `scene_check_route_edge_budget` (additional hypothesis: every edge it is given is normalised,
  `u ≤ v`). For one edge: `RouteInv` still holds afterwards; on error `required` is unchanged; on
  success `required` is unchanged if the edge was already present and has the edge appended otherwise.
  The branch that returns `InsufficientWorkspace` because `required` is already as long as the
  carrier's edge list is never taken: any `InsufficientWorkspace` the function returns is either the
  error it was handed or the error `Layout::doorway` returned for that edge.
- `scene_check_routes_required_exact` (no normalisation hypothesis). After `check_routes`, `RouteInv`
  holds. On success `required` is exactly the duplicate-free list of all route edges, in order of first
  occurrence. On error either the error is `InvalidGeometry`, `required` is unchanged and the number of
  routes differs from the number of circles, or the error comes from one identified failing route
  position.
- `scene_check_routes_ok_members`: on success `required` is duplicate-free and an edge is in it exactly
  when it is an edge of some route.

`Layout::doorway` can still return `InsufficientWorkspace`. The set of transforms a doorway depends on
has four slots; when the union for the two cells of an edge would need more, `doorway` returns that
error. It is not unreachable. See "Geometry totality" for what `doorway` is proved to return.

## Scene construction

Source: [`SceneConstruction.lean`](../lean/LabyrinthCore/SceneConstruction.lean),
`SceneInvNewTree.lean`, `SceneInvNewTreeFinal.lean`. All are partial correctness, with hypotheses:
the RNG adapter is legal (`constructorLegalRng`) and the layout's carrier is valid.

- `scene_new_spec`. Every result of `Scene::new` is one of the following, in this order:
  1. any of the eight storage-size checks fails: `Overflow`, RNG unchanged;
  2. the route check fails: its error, RNG unchanged;
  3. the spinning-portal scan fails: `InvalidGeometry`, RNG unchanged;
  4. building the carrier of the live edges fails: its error, RNG unchanged;
  5. creating the workspace fails: its error, RNG unchanged;
  6. the required-forest tree search fails: `Overflow` (the RNG may have advanced), or
     `InsufficientWorkspace` or `InvalidForest` with the RNG unchanged;
  7. the occupant table is invalid: `InvalidIndex`, with the RNG as the tree search left it;
  8. success. The scene has the given layout; the tree found by the search (valid on the live carrier,
     rooted at cell 0, containing every route edge); `required` equal to the route edges and contained
     in the live edges; both phase tables all zero; stamp `{epoch, 0}`; clock, wall and trail revision
     zero; latest request equal to the epoch; no pending request; not re-anchoring, suspended or
     inactive; RNG as the search left it.
- `scene_new_tree` (additional hypothesis: the carrier's cell count equals the layout's cell count). A
  returned scene's tree is `TreeValid` on the scene's own layout carrier.
- `scene_new_full_unconditional` (additional hypotheses: the layout satisfies the geometry invariant
  `LayoutGeom`, and the same cell-count equality). A returned scene satisfies `HoldLaw`,
  `EditCapacity` and `SceneInv`.

## Edits

Source: `ScenePreflight*.lean`, `SceneEditPublish.lean`, `SceneEditPrepare.lean`,
`SceneEditMotion.lean`, `SceneEditCarve.lean`, `SceneInvPrepare.lean`. An edit is a list of tree edges
to remove, an equal-length list of edges to add, and optionally replacement route cells.

- `scene_preflight_edit_spec` (partial correctness, no hypotheses). Order of checks: the two lists
  differ in length: `InvalidTransition`, scene unchanged; otherwise the removals are checked one by one
  and the first failing one's error is returned, scene unchanged; then the route check on the edited
  tree (error returned, scene unchanged except `required`); then every kept tree edge's doorway; then
  every added edge's doorway (errors, scene unchanged except `required`); otherwise success with the
  scene unchanged except `required`.
- `scene_preflight_edit_frame` (hypotheses: valid carrier, `RouteInv` on `required`). The returned
  scene always equals the input except for `required`, which stays duplicate-free and inside the
  carrier's edges.
- `scene_preflight_edit_accepted` (same hypotheses). When preflight accepts: removals and additions
  have equal length; every removal passed the occupancy check; `required` is exactly the duplicate-free
  list of the route edges that will be published; every such route edge is an edge of the edited tree;
  the number of routes equals the number of circles.
- `scene_commit_edit_spec` (total; hypotheses: the phase table is no longer than the scratch phase
  table, and replacement routes are no longer than the routes). The published phases are the scratch
  phases, route cells are replaced as the edit says and route circles are unchanged.
- `scene_motion_spec` and `scene_carve_spec` (partial correctness; hypotheses: `EditSafe` and
  `EditCapacity` on the input scene; `EditSafe` includes valid carrier, `TreeValid`, valid workspace,
  `RouteInv`, and that every route edge is an edge of the tree). Whatever is returned satisfies
  `EditSafe`. **An accepted edit preserves every route edge and tree validity**: the new tree's edge
  set is exactly the old one with the removals and additions applied, the layout is unchanged, routes
  are unchanged if the edit has no replacement routes and otherwise have exactly the replacement
  routes' edges, and the stamp is the returned stamp. For `carve` the published phases are also
  unchanged. **A rejected `motion` or `carve`** leaves the tree, layout, routes, published phases and
  stamp unchanged but rewrites three scratch fields: the required list, the next-phase table and the
  workspace.
- `prepare_motion_spec` (partial correctness, no hypotheses). Only the scratch phase table changes. If
  it accepts, the step list has as many entries as the published phase table, every step is between 0
  and 512, a nonzero step is accepted only on a transform whose hold counter is zero, and each scratch
  phase is `(phase + step) mod 4096`. `prepAccepted_held` (hypotheses: the call was accepted and the
  published phases lie in `[0, 4096)`) gives that every transform with a nonzero hold counter keeps its
  phase in the scratch table; `motion_phases_held` (additionally: the reservation invariant, and that
  the new published phases are the scratch table) gives that an accepted motion leaves the phase of
  every transform held by a crossing walker unchanged. This covers the first loop of `prepare_motion`
  only; `advance_motion` is covered in "The motion planner".

## Epoch and revision publication

Source: `ScenePublication.lean`, `SceneGeometryReject.lean`, `SceneSafetyTick.lean`. All total. A
"stamp" is an `(epoch, revision)` pair.

- `check_stamp_spec`: a wrong epoch gives `StaleEpoch`; a right epoch with a wrong revision gives
  `StaleRevision`; a right stamp at the maximum revision gives `Overflow`; otherwise it returns the
  next revision. `check_stamp_stale_epoch`, `check_stamp_stale_revision`, `check_stamp_overflow`,
  `check_stamp_ok` state the four cases separately.
- `suspend_spec`, `resume_spec`: a stamp that fails the check returns its error with the scene
  unchanged; a wall-clock value earlier than the scene's gives `InvalidTransition`, scene unchanged;
  otherwise the stamp's revision advances by one, the wall clock is set, and `suspended` is set (or
  cleared by `resume`, which also sets re-anchoring when a layout request is pending or the scene is
  inactive).
- `request_layout_spec`: after the stamp check, at the maximum request number it gives `Overflow`,
  scene unchanged; otherwise the revision advances, the request number advances by one and is
  returned, re-anchoring is set and the request is recorded as pending.
- `publish_layout_spec` (no hypotheses on the candidate). A request that is not the pending one or not
  the latest gives `StaleEpoch`; a candidate whose epoch is not the request gives `StaleEpoch`; a
  candidate whose revision is not zero gives `InvalidTransition`; all with the scene unchanged.
  Otherwise the candidate replaces the scene, keeping the current wall clock and suspended flag,
  setting re-anchoring and recording the request; the reply counts the walkers terminated (all of
  them) and the reservations released (the crossing walkers).
- `reject_layout_total` (hypothesis: `SceneGeom`, the layout geometry invariant, valid carrier and
  enough phase entries). The call always returns, and the result is one of: `StaleEpoch` (request not
  the pending and latest one), `InvalidGeometry` (bad viewport), `Overflow` (maximum revision), the
  error of the fit scan, each with the scene unchanged; or success, which advances the revision, clears
  the pending request and sets `inactive` exactly when the scan found the layout does not fit.
- `tick_spec` (hypothesis: the reservation invariant `ResInv`). Stamp failure gives its error, scene
  unchanged; an earlier wall clock gives `InvalidTransition`; a suspended, inactive or pending scene
  only advances revision and wall clock; a re-anchoring scene clears the flag; otherwise the clock
  advances by the elapsed wall time (`Overflow` if it would exceed the maximum) while holds, walkers
  and patches are updated and the reservation invariant is kept. Component lemmas: `tick_stale_epoch`,
  `tick_stale_revision`, `tick_revision_overflow`, `tick_wall_regressed`, `tick_frozen`,
  `tick_reanchored`, `tick_clock_overflow`, `tick_active`.

## Reservations

Source: `SceneReservation*.lean`, `SceneSafety.lean`, `SceneInvMotion.lean`, `SceneInvCarve.lean`.

- `admission_spec` (total). A cell index out of range gives `InvalidIndex`; a suspended, inactive or
  layout-pending scene gives `InvalidTransition`; a cell inside a patch gives `Occupied`; otherwise
  `Ok`.
- `reservation_spec` (total). A token with another epoch gives `StaleEpoch`; a walker index out of
  range gives `InvalidIndex`; a token that its walker does not hold gives `InvalidTransition`;
  otherwise the walker's crossing is returned.
- `begin_crossing_outcome` (partial correctness, no hypotheses). A failing stamp gives its error.
  Otherwise: walker index out of range `InvalidIndex`; walker not ready or duration zero
  `InvalidTransition`; admission failure at the walker's cell or at the target cell, that error; target
  not joined to the walker's cell by a tree edge `InvalidTransition`; a doorway error, that error; a
  saturated hold counter `Overflow`; all with the scene unchanged. Otherwise a reservation token is
  returned, the walker enters the crossing state with the doorway's corridor and path, and the hold
  counters of the transforms the doorway depends on are incremented.
  `begin_crossing_rejection_frame` (partial correctness, no hypotheses): every error leaves the whole
  scene unchanged.
- `check_removal_exact` (partial correctness, no hypotheses). Removing a non-tree edge gives
  `InvalidTransition`; a doorway error is returned as is; otherwise the result is `Occupied` exactly
  when some crossing walker's corridor meets the corridor of the removed edge's doorway, and `Ok`
  exactly when none does. The statement does not involve the hold counters: removal is blocked by the
  walkers' corridors only. (`scene_check_removal_spec` is the loop-level form.)
- `preflight_edit_safe`, `motion_safe`, `carve_safe`, `reform_patch_safe` (partial correctness).
  Hypotheses: `EditSafe` on the scene (and `EditCapacity` for `reform_patch_safe`), `LayoutGeom`, enough
  phase entries for the transforms, and `CrossFresh` (each crossing walker's edge is still a tree edge
  and the doorway recomputed for it has the corridor the walker recorded). Conclusion: whenever the
  operation accepts, none of its removed edges is an edge a walker is crossing.

## Shatter

Source: `SceneShatter*.lean`, `SceneSafety.lean`. A patch moves through the stages idle, draining,
parked, hidden, scattered, reforming and back to idle. `Frozen` means the scene is suspended,
inactive or has a pending layout request.

- `begin_shatter_spec` (total; hypotheses: every crossing walker stands at its crossing's source cell
  (`CrossAtSource`), and every patch's cell table has one entry per layout cell (`PatchRoom`)).
  A failing stamp gives its error; an empty cell list gives `InvalidSize`; a frozen scene gives
  `InvalidTransition`; a failing cell check gives its error; all with the scene unchanged. If every
  patch slot is in use the result is `InsufficientWorkspace`, scene unchanged. Otherwise the first idle
  slot is claimed with a fresh serial equal to the new revision, the draining sweep is applied to the
  walkers, and the patch id is returned.
- `hide_patch_spec` (total). Stamp failure, an invalid patch id (stale epoch, out of range, idle or
  wrong serial), or a frozen scene give
  their errors with the scene unchanged (`InvalidTransition` for frozen); a patch that is not parked
  gives `Occupied`, unchanged; otherwise the revision advances and the patch's walkers are set hidden.
- `scatter_patch_spec` (total). The same id and frozen failures; a patch not hidden or a zero duration
  gives `InvalidTransition`; a clock that would overflow gives `Overflow`; all unchanged. Otherwise the
  revision advances and the patch becomes scattered until the clock plus the duration.
- `reform_patch_spec` (partial correctness; hypotheses: `EditSafe`, `EditCapacity`). The same
  stamp, id and frozen failures; zero duration, or a patch that is not scattered with its time reached,
  gives `InvalidTransition`, unchanged; otherwise the checked edit is attempted.
- `reform_patch_headline` (same hypotheses). Whatever is returned satisfies `EditSafe`. A rejection
  rewrites only the three scratch fields (required list, next-phase table, workspace). On success every
  endpoint of every removed and added edge lies in the patch; the tree's edge set is exactly the old one
  with the edit applied; routes are unchanged or have exactly the replacement routes' edges; layout,
  holds, walkers, clock, wall clock, phases and the layout flags are unchanged; the revision advances by
  one; and the patch enters the reforming stage with deadline clock plus duration. It is the only shatter
  operation that edits the topology, and it is the same checked edit as `carve`, confined to the patch.
- Stage order: `StageNext` is the relation of allowed stage steps (idle to draining, draining to
  parked, parked to hidden, hidden to scattered, scattered to reforming, reforming to idle).
  `tick_patch_progress` (an equational statement about the pure patch-update functions, no
  hypotheses) says one tick leaves a patch's stage unchanged or moves
  it by one `StageNext` step, keeps its serial and cells, never parks a patch that still touches a
  walker, and returns an expired patch to idle.

## Geometry totality

Source: `SceneGeometry*.lean`, `SceneInvNewTreeFinal.lean`, `ConstructorCarrierRowsErrors.lean`.

- `layout_new_total_closed` (total). **Hypothesis `LayoutCapacity`: the total number of cells
  `Layout::new` creates, namely the grid cells, the cells of every circle and one per portal
  transition, is at most `usize::MAX`.** It is a hypothesis on the inputs alone. Totality is proved only
  when the cell total is representable, because the proof needs the index arithmetic over all cells not
  to overflow; no statement is made for larger inputs. Under it `Layout::new` always returns, a returned
  layout satisfies `LayoutGeom`, has a valid carrier, satisfies the centre-radius floor and has one
  cell per carrier vertex, and a returned error is one of `InvalidGeometry`, `InvalidSize`, `Overflow`,
  `InvalidIndex`, `InsufficientWorkspace`, `InvalidCarrier`, `Disconnected`.
- `layout_new_geom` (partial correctness, no hypotheses): any layout `Layout::new` returns satisfies
  `LayoutGeom` and has a valid carrier.
- `layout_doorway_total` (total; hypotheses: `LayoutGeom`, valid carrier, and both phase tables at
  least as long as the transform count). `Layout::doorway` always returns; an `Ok` doorway has an edge of
  the carrier, a corridor within bounds and a valid hold set; an error is one of `InvalidIndex`,
  `InvalidGeometry`, `InsufficientWorkspace`. `layout_new_doorway_total` is the same for a layout that
  `Layout::new` returned, with no layout hypotheses.
- `doorway_minimum_exact` (total; hypotheses: margin in `(0, 1000000]`, centre radius at least four
  margins and at most 1000000, radii in `[0, 1000000]`): the minimum subdivision count is
  `(2·margin·4096 + radius − 1) / radius` (integer division) for some radius between four margins and
  1000000, lies in `[1, 2048]`, and the computation does not fail.
- `grid_rect_touches_disk_total` (total; hypotheses: a well-formed rectangle and a point within
  bounds): `Rect::touches_disk` always returns, and is true exactly when the squared distance from the
  point to the rectangle is at most the squared radius.
- `from_edges_error_set` (partial correctness, no hypotheses): `Carrier::from_edges` returns only
  `InvalidSize`, `InvalidIndex`, `InvalidCarrier`, `Disconnected` or `Overflow` as errors.

## One scene invariant and reachability

`SceneInv` is the conjunction of: `EditSafe` (valid carrier, `TreeValid` tree, valid workspace,
workspace large enough for the tree, `RouteInv` on the required list, phase tables ordered, one route
per circle, every route edge a tree edge); `EditCapacity` (the workspace edge capacity covers the
carrier's edges); `LayoutGeom`; enough phase entries for the transforms; phases in `[0, 4096)`; the
reservation invariant; every crossing walker's recorded doorway is still a tree edge with the same
corridor and holds (`CrossHeld`); and `PatchRoom`. `HoldLaw` says every hold counter equals the
number of crossing holds on that transform, and every patch that is neither idle nor draining
touches no walker.

Each operation keeps the invariant. All are partial correctness, with `SceneInv` on the input scene as
hypothesis (and on the candidate for publication): `suspend_inv`, `resume_inv`, `request_layout_inv`,
`reject_layout_inv`, `publish_layout_inv` (hypothesis: `SceneInv` on the candidate scene too),
`begin_crossing_inv`, `motion_inv`, `carve_inv`, `tick_inv`, `swept_doorway_inv` (hypothesis `SceneInv`
and `HoldLaw`; concludes both), `begin_shatter_inv`, `hide_patch_inv`, `scatter_patch_inv`,
`reform_patch_inv`. For construction, `scene_new_inv` gives `HoldLaw` and, given `EditSafe` and
`EditCapacity` on the result, `SceneInv` (see "Scene construction" for the unconditional form).
`holdLaw_*` and `*_holdLaw` lemmas carry `HoldLaw` through the same operations.

`SceneReachableU` is the set of scenes obtained from a successful `Scene::new` on a layout that
`Layout::new` accepted, by any sequence of calls that return, among exactly these fourteen
operations (`advance_motion` is covered separately in "The motion planner"): `suspend`, `resume`,
`request_layout`, `reject_layout`, `publish_layout` (the candidate
must itself be reachable), `begin_crossing`, `motion`, `carve`, `tick`, `swept_doorway`,
`begin_shatter`, `hide_patch`, `scatter_patch`, `reform_patch`. A call counts whether it returned
success or an error; only that it returned matters.

- `sceneReachable_inv_unconditional` (partial correctness, no further hypotheses): every scene in
  `SceneReachableU` satisfies `SceneInv` and `HoldLaw`.
- `sceneReachableU_hold_exact`: in every such scene each hold counter is exactly the number of
  crossing holds on that transform.
- `reachable_no_leaked_hold` (stated for `SceneReachable`, the same set with the construction case
  assuming a valid tree on the layout carrier; `sceneReachableU_toReachable` converts one to the
  other): a positive hold counter is held by a crossing walker, so when no crossing walker holds a
  transform its counter is zero (`reachable_unheld_zero`).

Reachability is only about operations that are listed. Other public functions are not covered by it.

## The motion planner

Source: `SceneMotionAdvance.lean`, `SceneMotionReach.lean`, `SceneMotionConnected.lean`,
`SceneMotionFrame.lean`. All statements here are **partial correctness**: they hold of every result
`advance_motion` returns, and say nothing about whether it returns. `advance_motion` validates the
request with `prepare_motion`, lets the planner propose an edit for a divided step table, and
publishes through one final `Scene::motion` call, which re-checks everything it publishes.

- `advance_motion_scene`: every outcome is either an error on a scene that differs from the input only
  in the scratch phase table (same length), or exactly what `Scene::motion` returns on such a scene,
  and an accepted advance carries the same event as that motion. Supporting lemmas: `NextOf`
  (`nextOf_refl`, `nextOf_trans`), `prepare_motion_next`, `advance_loop2_next`, `advance_early`,
  `advance_publish`, `advance_scene`, `sceneInv_next`, `holdLaw_next`, `sceneInvFull_next`.
- `advance_motion_inv` (hypothesis: `SceneInv` and `HoldLaw` on the input scene). **Whatever it
  returns, success or error, the returned scene satisfies `SceneInv` and `HoldLaw`.**
- `advance_motion_safe` (hypothesis: `SceneInv` on the input scene). On success, every edge between
  the source and target of a crossing walker that was a tree edge before is still a tree edge, and
  every transform with a nonzero hold counter keeps its published phase.
- `advance_motion_connected` (hypothesis: `SceneInv` on the input scene). On success the layout is
  unchanged, the new tree is `TreeValid` on the layout's carrier, every route edge is an edge of the
  new tree, and one of two things holds: nothing moved (tree, published phases and routes are all
  unchanged), or the published phases are a table `np` (the new published phases equal `np` at every
  transform) such that every edge of the new tree has a doorway that `Layout::doorway` accepts between
  the old phases and `np`. This does **not** pair each removed edge with a replacement chosen for it
  and says nothing about why the planner picked the edit it did; it says that no tree edge whose
  doorway became inadmissible survives the accepted motion. Supporting lemmas: `motion_door`,
  `motion_commit_door`, `preflight_doors`, `kept_door`, `added_door`.
- Reachability with `advance_motion`. `SceneReachableM` is `SceneReachableU`'s construction case (here
  with the additional assumption that the new scene's tree is valid on the layout carrier, as in
  `SceneReachable`) plus the fourteen operations above plus `advance_motion`: **fifteen operations**.
  `sceneReachable_motion` shows it contains everything `SceneReachable` does. Corollaries, all partial
  correctness and with no further hypotheses on the scene: `sceneReachableM_inv` (every such scene
  satisfies `SceneInv` and `HoldLaw`), `reachableM_hold_exact` (every hold counter equals the number
  of crossing holds), `reachableM_no_leaked_hold`, `reachableM_advance_motion_safe` and
  `reachableM_advance_motion_connected` (the two statements above on every such scene).
- Workspace frame (`WFrame`). The planner's workspace fields that bind it to a scene (`epoch`, `cells`,
  `edges`, `endpoints`), the divided steps, the `admissible` and `locked` flags and the split-vertex
  network (`from`, `to`, `offsets`, `arcs`) are not written by the search helpers: `clear_search_frame`,
  `augment_frame`, `residual_path_frame`, `flow_path_frame`, `reset_flow_frame`, `tree_path_frame`,
  `route_through_frame`, `plan_route_frame` (and their loop forms), with `wFrame_refl`.
- `plan_ok_balanced`: an accepted plan proposes as many added edges as removed edges.

## Not proved

- **The motion planner's liveness.** There is no theorem that `advance_motion`, `MotionWorkspace::advance`
  or `plan` always return (no panic, no divergence), and none that the planner always proposes an edit
  that `Scene::motion` accepts, so an advance can still end in an error. The same holds for the
  totality and the search behaviour of `plan`, `route_through`, `flow_path` and the rest of the search.
  The statements in "The motion planner" speak only of results that are returned.
- **The exact specifications of the planner's leaf helpers**: `MotionWorkspace::new`, `check_scene`,
  `eligible`, `arc_pair`, `edge_index`, `virtual_edge`, `check_route_endpoints`, `route_admissible`,
  `network_sizes`, `motion_edge`, and what the flow, residual and tree-path searches compute
  (shortest or feasible paths, flow value). Only that they leave the listed workspace fields alone is
  proved. The planner's own claim that every sector-boundary event is connected is therefore proved
  only in the checked form given in "The motion planner" (the accepted edit leaves a valid tree whose
  edges all have doorways), not as a statement about the planner's choices.
- Functions with no theorem and not named by any proof file: `tree::reaches` and `tree::random_reparent`
  (no theorem; `set_parent_spec` is only about the update and the error cases); the polar projection and
  ring/sector helpers (`polar::project`, `Circle::offset_at`, `ring_offset`, `sector`, `sector_arc`,
  `outer_radius`, `transform_start`, `center_cell`); the interpolation and pose helpers
  (`walker::interpolate`, `interpolate_angle`, `Walker::local_pose`, `Path::pose`,
  `Scene::walker_pose`); `Scene::check_patch_motion`, `Scene::doorway_bounds`,
  `Layout::adapter_band`, `Layout::transform_count`, `Rect::contains_point`,
  `walker::Crossing::edge`, `Carrier::is_empty`, and the plain accessors (`Scene::is_suspended`,
  `is_inactive` and field getters). Some of these are exercised inside larger proofs by unfolding, but
  no statement is about them.
- Termination and panic freedom of any operation whose theorem above is marked partial correctness.
- Probabilities and uniformity of random choices, solver and difficulty metrics, DFS tie-breaking
  distributions.
- Floating-point geometry beyond the extracted integer model, Wasm and browser behaviour, native/Wasm
  equivalence, and 32-bit `usize` behaviour. No Wasm or browser result is claimed.
- The conservative spinning-admission bounds may reject some geometrically feasible layouts; no
  completeness statement is proved.

## Reproduce

Use the revisions in [`toolchain-pins.json`](../toolchain-pins.json) and the dependency lock
[`lean/lake-manifest.json`](../lean/lake-manifest.json). Upstream build prerequisites and
source references are recorded in the [research notes](research/2026-11-06-algorithm-and-verification.md#rust-to-lean-tooling).

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
cargo run --release --manifest-path tools/check/Cargo.toml
```

The runner checks translator source revisions and the Aeneas executable version, then extracts
the actual crate into temporary Lean files. They must byte-match the checked-in generated
definitions before `lake build` checks them with warnings treated as errors. Drift fails the
gate without overwriting the checked-in model.

Extraction passes the three Charon `--include` patterns
(`core::slice::{impl core::default::Default for &Slice<_>}::default`,
`core::option::{impl core::default::Default for core::option::Option<_>}::default`,
`core::result::_::is_err`) and the Aeneas flag `-all-computable`. The generated
`FunsExternal_Template.lean` must list exactly the eight modeled externals; the repo
`lean/LabyrinthCore/FunsExternal.lean` supplies their definitions.

Two text scans precede the build. The generated `Types.lean`/`Funs.lean` and the repo
`FunsExternal.lean` must declare no axiom: no line may start with `axiom`, also after
`@[...]` attributes and the `private`, `protected`, `noncomputable`, `unsafe`, `partial` and
`nonrec` modifiers. No file under `lean/` (outside `lean/.lake`) may contain `skipKernelTC`
(the `debug.skipKernelTC` option) or `addDeclWithoutChecking` (the environment function it
selects); both add declarations without kernel type checking.

The imported axioms of every theorem listed in `lean/Audit.lean` must be drawn only from
`propext`, `Classical.choice`, and `Quot.sound`; an unrecognized audit result also fails. A
separate Lean fixture relying on an application-defined axiom exercises this rejection.

The runner then copies the Rust source into a temporary directory, changes the indexed
assignment in `tree::set_parent` to store `child` instead of `new_parent`, and independently
extracts and compiles that incorrect operation. The unchanged `set_parent_spec` must report an
unsolved proof goal. A compiler/translation failure is not accepted as evidence that the
specification rejects the mutation. Temporary checks reuse compiled dependencies without
rebuilding shared caches.

For the native checks, use the same isolated Cargo/Rustup environment and run from `rust/`:

```sh
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo doc --no-deps
```

The native scenarios are executions, not universal proofs.

## Trust and limitations

Every root of `lean/Audit.lean` imports only `propext`, `Classical.choice` and `Quot.sound`. No
application axiom, `sorry`, `admit`, native-evaluation axiom or skipped proof obligation is used.
`lean/Audit.lean` prints the transitive axiom inventory, and the runner fails on any other result.
Kernel type checking is not disabled: the runner rejects `debug.skipKernelTC` and
`addDeclWithoutChecking` anywhere under `lean/`.
The generated `Types.lean` and `Funs.lean` byte-match a fresh extraction of the Rust source.

These are proofs about the extracted Lean model of the crate, under the model limits below. Trusted
components include the pinned Rust compiler/MIR, Charon extraction, Aeneas translation and
standard-library models, imported Lean/Mathlib infrastructure, and the Lean kernel. The Lean theorems
do not independently certify those translators, native machine code, LLVM, Wasm compilation, browser
bindings, or allocation failure. Source-revision/version checks are not a reproducible-build
attestation of tool binaries. The runner's mutation check covers `set_parent_spec` only.

Construction cost is also outside the model: `Layout::new` allocates and scans
`columns × rows` grid slots and aborts on allocation failure, and `Carrier::from_csr` validation is
O(Σ deg²). The caller bounds grid size and row degree.

The extraction runs on stock Aeneas `87cfe2f5` with no fork or patch. Stock Aeneas leaves eight
external operations as templates (`alloc.vec.Vec.clear`, `core.num.I32.abs`,
`core.num.I32.rem_euclid`, `core.ops.range.RangeInclusive.contains`, and the `Option`
`clone`, `eq`, `Debug::fmt` and `copied` models). The repo-owned
[`FunsExternal.lean`](../lean/LabyrinthCore/FunsExternal.lean) defines them, plus
`Aeneas.Std.I32.div`, which stock Aeneas prints for overflow-unchecked signed division but Std
does not define. That is nine real definitions and no application axioms. Model limits:

1. Stock `IScalar.rem` returns `BitVec.srem`, so `MIN % -1 = ok 0` where Rust panics; the same
   holds for `core.num.I32.rem_euclid`. Every signed remainder in the crate has a positive
   constant divisor (`polar.rs` `rem_euclid(TURN)` and `% (TURN / 4)`), so this is unreachable here.
   `i32_rem_euclid_spec` assumes a positive modulus.
2. `Vec::clear` is content-level: the model `Vec` has no capacity.
3. `Option` `Debug::fmt` preserves the branch relative to the existing formatter abstraction and
   makes no claim about the produced text.

The executed native target is `aarch64-apple-darwin`, with 64-bit `usize`. The generated model
uses Aeneas `Usize`; this is not evidence of 32-bit Wasm parity. Width-sensitive arithmetic
and native/Wasm equivalence are not established.

To review the correspondence by hand, read the Rust module, its generated
[`Funs.lean`](../lean/LabyrinthCore/Funs.lean), and the theorem named in the section above together.
The hypotheses stated with each theorem apply.

## Implementation status (executions, not proofs)

The native crate implements validated CSR carriers, ordinary DFS, required-forest
contraction/quotient DFS/expansion, sparse tree edits, combined grid/polar layouts, reservations,
shatter, suspension and epoch replacement. `Scene::advance_motion` performs production
boundary-event planning with reusable flow/search storage and sparse edge proposals. What is proved
about it (partial correctness only) is in "The motion planner"; that it always returns and always
proposes an acceptable edit is not proved.

Spinning admission uses conservative radius/clearance bounds. `Scene::new` checks the chosen exterior
portal pair over every quantized one-unit outer-ring sweep; this check runs only at construction.
An edit through `Scene::motion` that replaces a route is checked on the current interval only, so a
replacement that changes or reverses the portal pair can leave that ring unable to advance (safety
is unaffected; this is a liveness limit). Some geometrically feasible
layouts can be rejected by these conservative bounds. Accepted proposals still pass the
geometry, route, reservation and tree checks before publication. The returned positive subdivision
divisor specifies the consumed phase increments.

Native tests cover multiple circles, unequal ring counts/sectors, impossible spinning layouts,
safe resized high-sector layouts, reserved crossings, stale workspaces and atomic rejection.
The seeded native example traverses grid → polar interior → different portal → grid in both
modes and completes three motion periods. A counting-allocator test (`rust/tests/allocations.rs`)
observes zero allocations across repeated `Tree::reroot`, `Tree::exchange` and `Tree::edit_edges`
calls once the tree and its workspace exist. No test measures allocations of crossings, ticks or
`Scene::advance_motion`. These are execution results, not universal proofs or browser acceptance.
