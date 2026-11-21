module
public import LabyrinthCore.SceneInvNewWork

/-! The scene invariant, part 13: the edit preconditions of the scene `Scene::new` returns.

The workspace has the layout carrier's edge count as capacity (`Workspace::new`) and keeps it and
its path length through `scene_dfs`; the tree's cells fit the path; the route-edge scratch list is
duplicate-free inside the carrier; the saved routes have the route cells, one route per circle; and
every route edge is a tree edge. That is `EditCapacity` and every part of `EditSafe` except one: the
tree `scene_dfs` returns is valid on the carrier of the live edges, and `EditSafe` asks for validity
on the layout's carrier, of which the live edges are a subset. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem allEdges_congr : ∀ (l1 l2 : List scene.Route),
    l1.map (fun r => r.cells.val) = l2.map (fun r => r.cells.val) → allEdges l1 = allEdges l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, b :: u, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := allEdges_congr t u h.2
    unfold allEdges at ih ⊢
    simp only [List.flatMap_cons]
    rw [h.1, ih]

/-- The route copy loop of `Scene::new` copies every route's cells. -/
theorem new_routes_copy (routes : Slice scene.Route) (count : Std.Usize)
    (saved : alloc.vec.Vec scene.Route) (hs : saved.val = []) :
    OkPost (scene.Scene.new_loop1 routes count saved 0#usize)
      (fun y => y.val.map (fun r => r.cells.val) = routes.val.map (fun r => r.cells.val)) := by
  unfold scene.Scene.new_loop1
  refine okPost_loop (fun s : alloc.vec.Vec scene.Route × Std.Usize => s.2.val ≤ routes.val.length ∧
      s.1.val.map (fun r => r.cells.val) = (routes.val.take s.2.val).map (fun r => r.cells.val))
    _ _ ?_ _ ⟨by simp, by simp [hs]⟩
  rintro ⟨sv, i⟩ ⟨hi, hsv⟩
  simp only at hi hsv
  unfold scene.Scene.new_loop1.body
  by_cases hlt : i < Slice.len routes
  · simp only [hlt, ↓reduceIte]
    have hl : i.val < routes.val.length := by simpa using hlt
    refine okPost_bind_eq (okPost_trivial _) (fun r hr _ => ?_)
    have hri : routes.val[i.val]? = some r := slice_index_some hr
    refine okPost_bind (okPost_of_spec (vec_extend_usize _ _ (by
      simp [with_capacity_val]))) (fun c hc => ?_)
    refine okPost_bind (vec_push_okPost _ _) (fun sv1 hsv1 => ?_)
    refine okPost_bind (okPost_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by
      have := routes.property; simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) (fun i2 hi2 => ?_)
    have hi2v : i2.val = i.val + 1 := by simpa using hi2
    refine okPost_ok ⟨show i2.val ≤ routes.val.length by omega, ?_⟩
    show sv1.val.map (fun r => r.cells.val) = (routes.val.take i2.val).map (fun r => r.cells.val)
    rw [hsv1, hi2v, List.take_add_one, hri]
    simp only [List.map_append, hsv, Option.toList, List.map_cons, List.map_nil]
    rw [hc, with_capacity_val]
    simp [alloc.vec.Vec.deref]
  · simp only [hlt, ↓reduceIte]
    have : ¬ i.val < routes.val.length := by simpa using hlt
    refine okPost_ok ?_
    show sv.val.map (fun r => r.cells.val) = routes.val.map (fun r => r.cells.val)
    rw [hsv, List.take_of_length_le (by omega)]

/-- What the edit preconditions need of a scene `Scene::new layout routes ...` returns. -/
def NewEditFacts (layout : scene.Layout) (routes : Slice scene.Route) (s : scene.Scene) : Prop :=
  WorkspaceValid s.work ∧ s.tree.parents.val.length ≤ s.work.path.val.length ∧
  RouteInv layout.carrier s.required ∧ routes.val.length = layout.circles.val.length ∧
  s.routes.val.map (fun r => r.cells.val) = routes.val.map (fun r => r.cells.val) ∧
  (∀ e ∈ allEdges routes.val, parentEdge (parents s.tree) e.u.val e.v.val) ∧
  layout.carrier.edges.val.length ≤ s.work.edge_capacity.val

/-- **The edit preconditions of `Scene::new`**: everything but the tree's validity on the layout
carrier. -/
theorem scene_new_edit_facts {R : Type _} (treeRngInst : tree.Rng R)
    (hrng : constructorLegalRng treeRngInst) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hc : CarrierValid layout.carrier) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → NewEditFacts layout routes s) := by
  by_cases hpass : SceneStoragePass layout routes occupants patch_capacity
  swap
  · rw [scene_new_not_pass treeRngInst layout routes occupants patch_capacity epoch rng hpass]
    exact okPost_ok (fun s h => by simp at h)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpass
  rw [scene_new_checks_pass treeRngInst layout routes occupants patch_capacity epoch rng h1 h2
    h3 h4 h5 h6 h7 h8]
  unfold sceneNewTail
  refine okPost_bind (okPost_trivial _) (fun phases _ => ?_)
  have hedges : topology.Carrier.impl.edges layout.carrier =
      ok (alloc.vec.Vec.deref layout.carrier.edges) := rfl
  rw [hedges, Std.bind_ok]
  refine okPost_bind (okPost_trivial _) (fun e _ => ?_)
  have hinv0 : RouteInv layout.carrier (alloc.vec.Vec.with_capacity topology.Edge
      (Slice.len (alloc.vec.Vec.deref layout.carrier.edges))) := by
    rw [RouteInv, with_capacity_val]; simp
  refine okPost_bind_eq (scene_check_routes_required_exact layout routes
    (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) none e _ hc hinv0) ?_
  rintro ⟨r8, required1⟩ hcall ⟨hreq, _, _⟩
  simp only at hreq
  cases r8 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok (fun s h => by simp at h)
  | Ok u =>
    have hrl : routes.val.length = layout.circles.val.length := by
      unfold scene.check_routes at hcall
      by_cases hne : (Slice.len routes != alloc.vec.Vec.len layout.circles) = true
      · simp [hne] at hcall
      · simpa [Slice.len] using hne
    dsimp only
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
      alloc.vec.Vec.deref_mut]
    refine okPost_bind (okPost_trivial _) ?_
    rintro ⟨r9, s5, s6⟩ _
    cases r9 with
    | Err x =>
      simp only [Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact okPost_ok (fun s h => by simp at h)
    | Ok u =>
      simp only [Std.bind_ok]
      refine okPost_bind (okPost_trivial _) (fun live1 _ => ?_)
      refine okPost_bind_eq (okPost_of_spec
        (constructor_carrier_from_edges_total_spec (alloc.vec.Vec.len layout.cells)
          (alloc.vec.Vec.deref live1))) ?_
      intro r10 _ hcarrier
      cases r10 with
      | Err x =>
        simp only [Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        exact okPost_ok (fun s h => by simp at h)
      | Ok carrier =>
        simp only [Std.bind_ok]
        simp only at hcarrier
        refine okPost_bind_eq (okPost_of_spec (constructor_workspace_new_spec
          (alloc.vec.Vec.len layout.cells)
          (Slice.len (alloc.vec.Vec.deref layout.carrier.edges)))) ?_
        intro r11 _ hworkspace
        cases r11 with
        | Err x =>
          simp only [Std.bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          exact okPost_ok (fun s h => by simp at h)
        | Ok work =>
          simp only [Std.bind_ok]
          simp only at hworkspace
          obtain ⟨hwv, _, hcapw⟩ := hworkspace
          refine okPost_bind (okPost_and (okPost_of_spec (constructor_scene_dfs_spec treeRngInst
            hrng carrier (alloc.vec.Vec.deref required1) 0#usize rng work hcarrier hwv))
            (scene_dfs_frame treeRngInst carrier (alloc.vec.Vec.deref required1) 0#usize rng
              work)) ?_
          rintro ⟨r12, rng1, val4⟩ ⟨hd, hfc, hfp, hfle⟩
          simp only at hd hfc hfp hfle
          cases r12 with
          | Err x =>
            simp only [Std.bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok]
            exact okPost_ok (fun s h => by simp at h)
          | Ok tree =>
            simp only [Std.bind_ok]
            obtain ⟨pub, hpub, _, htv, hwv4, hslots⟩ :
                ∃ pub : spanning_tree.Tree, core.result.Result.Ok tree =
                    core.result.Result.Ok pub ∧ pub.root = 0#usize ∧ TreeValid carrier pub ∧
                  WorkspaceValid val4 ∧
                  (∀ slot, slot < (alloc.vec.Vec.deref required1).val.length → ∀ edge,
                    (alloc.vec.Vec.deref required1).val[slot]? = some edge →
                    parentEdge (parents pub) edge.u.val edge.v.val) := by
              rcases hd with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact h
              · simp at h
              · simp at h
              · simp at h
              · rcases h with h | ⟨h, _⟩ <;> simp at h
            simp only [core.result.Result.Ok.injEq] at hpub
            subst hpub
            have hreq1 := (scene_check_routes_required_exact layout routes
              (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) none e _ hc hinv0 _
              hcall).2.1 rfl
            simp only at hreq1
            have hall : ∀ x ∈ allEdges routes.val,
                parentEdge (parents tree) x.u.val x.v.val := by
              intro x hx
              have hxr : x ∈ required1.val := by
                rw [hreq1, foldEdges_mem]; exact Or.inr hx
              obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxr
              exact hslots j (by simpa [alloc.vec.Vec.deref] using hj) x (by
                simpa [alloc.vec.Vec.deref, List.getElem?_eq_getElem hj] using hjx)
            have hplen : tree.parents.val.length ≤ val4.path.val.length := by
              have := htv.1
              simp only [parents, List.length_map] at this
              rw [this, hfp]
              exact hfle tree rfl
            refine okPost_bind (new_routes_copy routes _ _ (with_capacity_val _)) ?_
            intro saved hsaved
            refine okPost_bind (okPost_trivial _) (fun pr6 _ => ?_)
            split
            · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
              refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
              refine okPost_ok (fun s hs => ?_)
              simp only [core.result.Result.Ok.injEq] at hs
              subst hs
              refine ⟨hwv4, hplen, hreq, hrl, hsaved, hall, ?_⟩
              show layout.carrier.edges.val.length ≤ val4.edge_capacity.val
              rw [hfc, hcapw]
              simp [deref_val]
            · exact okPost_ok (fun s h => by simp at h)

/-- **`Scene::new` establishes the scene invariant and the hold law**, once the tree it returns is
valid on the layout's carrier (it is valid on the carrier of the live edges). -/
theorem scene_new_full {R : Type _} (treeRngInst : tree.Rng R)
    (hrng : constructorLegalRng treeRngInst) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hc : CarrierValid layout.carrier) (hL : LayoutGeom layout) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → HoldLaw s ∧ EditCapacity s ∧
        (TreeValid s.layout.carrier s.tree → SceneInv s)) := by
  refine okPost_mono (okPost_and
    (scene_new_facts treeRngInst layout routes occupants patch_capacity epoch rng)
    (scene_new_edit_facts treeRngInst hrng layout routes occupants patch_capacity epoch rng hc))
    (fun p hp s hs => ?_)
  have hnf := hp.1 s hs
  obtain ⟨hwv, hplen, hreq, hrl, hsaved, hall, hcap⟩ := hp.2 s hs
  obtain ⟨hlaw, hg, htr, hpr, hres, hcr, hroom⟩ := newFacts_inv hnf hL
  have hlay : s.layout = layout := hnf.1
  have hcap' : EditCapacity s := by unfold EditCapacity; rw [hlay]; exact hcap
  refine ⟨hlaw, hcap', fun htv => ⟨⟨by rw [hlay]; exact hc, htv, hwv, hplen,
    by rw [hlay]; exact hreq, ?_, ?_, ?_⟩, hcap', hg, htr, hpr, hres, hcr, hroom⟩⟩
  · rw [hnf.2.2.2.2.1, hnf.2.2.2.2.2.2]
  · rw [hlay]
    have := congrArg List.length hsaved
    simp only [List.length_map] at this
    rw [this, hrl]
  · intro x hx
    rw [allEdges_congr _ _ hsaved] at hx
    exact hall x hx

end Labyrinth
