module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.ConstructorCarrierEdgeRows
public import LabyrinthCore.SceneInvNewEdit

/-! The scene invariant, part 12: the tree of the scene `Scene::new` returns is valid on the
layout's carrier.

`Layout::new` builds its carrier with `Carrier::from_edges(cells.len(), ..)`, so the carrier has
exactly as many cells as the layout (`layout_new_carrier_cells`). `Scene::new` builds its tree on
the carrier of the live edges, again over `cells.len()` cells, and the live edges are carrier
edges. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The carrier of a layout `Layout::new` accepts has one cell per layout cell. -/
theorem layout_new_carrier_cells (grid_spec : grid.GridSpec)
    (specs : alloc.vec.Vec polar.PolarSpec) (ps : Slice polar.PortalSpec)
    (geometry : grid.Geometry) :
    OkPost (scene.Layout.new grid_spec specs ps geometry)
      (fun r => ∀ L, r = .Ok L → cellCount L.carrier = L.cells.val.length) := by
  unfold scene.Layout.new
  have hres : ∀ (residual : core.result.Result Never topology.Error),
      OkPost (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual scene.Layout
        (core.convert.FromSame topology.Error) residual)
        (fun r => ∀ L, r = .Ok L → cellCount L.carrier = L.cells.val.length) :=
    fun residual => okPost_residual_gen residual (fun e L h => by cases h)
  refine okPost_any (fun r => ?_)
  cases r with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u =>
  refine okPost_branch_ok u _ ?_
  refine okPost_any (fun r1 => ?_)
  cases r1 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok m =>
  refine okPost_branch_ok m _ ?_
  refine okPost_any (fun i => ?_)
  by_cases hcs : grid_spec.cell_size < i <;> simp only [hcs, ↓reduceIte]
  · exact okPost_ok (fun L h => by cases h)
  refine okPost_any (fun r2 => ?_)
  cases r2 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok val1 =>
  refine okPost_branch_ok val1 _ ?_
  refine okPost_any (fun r3 => ?_)
  cases r3 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u3 =>
  refine okPost_branch_ok u3 _ ?_
  refine okPost_any (fun r4 => ?_)
  cases r4 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u4 =>
  refine okPost_branch_ok u4 _ ?_
  refine okPost_any (fun iter => ?_)
  refine okPost_any (fun a0 => ?_)
  obtain ⟨circles1, transforms, status⟩ := a0
  cases status with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u5 =>
  refine okPost_branch_ok u5 _ ?_
  refine okPost_any (fun bands => ?_)
  refine okPost_any (fun counts => ?_)
  refine okPost_any (fun a1 => ?_)
  obtain ⟨status1, bands1, counts1⟩ := a1
  cases status1 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u6 =>
  refine okPost_branch_ok u6 _ ?_
  refine okPost_any (fun status2 => ?_)
  cases status2 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u7 =>
  refine okPost_branch_ok u7 _ ?_
  refine okPost_any (fun a2 => ?_)
  obtain ⟨cell_grid, cells⟩ := a2
  refine okPost_any (fun a3 => ?_)
  obtain ⟨circles2, cells1⟩ := a3
  refine okPost_any (fun a4 => ?_)
  obtain ⟨status3, cells2, portals1⟩ := a4
  cases status3 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u8 =>
  refine okPost_branch_ok u8 _ ?_
  refine okPost_any (fun b => ?_)
  cases b
  case true => simp only [↓reduceIte]; exact okPost_ok (fun L h => by cases h)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine okPost_any (fun o => okPost_any (fun r5 => ?_))
  cases r5 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u9 =>
  refine okPost_branch_ok u9 _ ?_
  refine okPost_any (fun _ => okPost_any (fun _ => okPost_any (fun _ => ?_)))
  refine okPost_spec (constructor_carrier_from_edges_rows_spec _ _) (fun r6 hr6 => ?_)
  cases r6 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok carrier =>
  refine okPost_branch_ok carrier _ ?_
  refine okPost_any (fun _ => okPost_any (fun r7 => ?_))
  cases r7 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u10 =>
  refine okPost_branch_ok u10 _ ?_
  refine okPost_ok (fun L hL => ?_)
  cases hL
  exact hr6.2.1

/-- The adjacency of a carrier is symmetric. -/
theorem carrierEdge_symm {c : topology.Carrier} (hc : CarrierValid c) {u v : Nat}
    (h : carrierEdge c u v) : carrierEdge c v u := by
  obtain ⟨hu, hv⟩ := h
  obtain ⟨hvlt, hback⟩ := (hc.2.2.2.2.1 u hu).2.2 v hv
  exact ⟨hvlt, hback⟩

/-- An edge of a valid carrier's edge list is an adjacency in both directions. -/
theorem carrier_edge_mem_adj {c : topology.Carrier} (hc : CarrierValid c) {e : topology.Edge}
    (he : e ∈ c.edges.val) : carrierEdge c e.u.val e.v.val ∧ carrierEdge c e.v.val e.u.val := by
  have hmem : (e.u.val, e.v.val) ∈ edgePairs c := by
    unfold edgePairs
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have h := ((hc.2.2.2.2.2.2.2) e.u.val e.v.val).mp hmem
  exact ⟨h.2, carrierEdge_symm hc h.2⟩

/-- **Row-soundness consequence.** A carrier whose adjacency is that of a list of edges drawn from
a valid carrier's edge list has its adjacency inside that carrier, and its edge pairs are edge
pairs of that carrier. -/
theorem carrier_sub_of_rows {big small : topology.Carrier} (hbig : CarrierValid big)
    (hsmall : CarrierValid small) (live : List topology.Edge)
    (hsub : ∀ e ∈ live, e ∈ big.edges.val)
    (hrows : ∀ u v, carrierEdge small u v ↔
      ∃ e ∈ live, (u = e.u.val ∧ v = e.v.val) ∨ (u = e.v.val ∧ v = e.u.val)) :
    (∀ u v, carrierEdge small u v → carrierEdge big u v) ∧
    (∀ p, p ∈ edgePairs small → p ∈ edgePairs big) := by
  have hadj : ∀ u v, carrierEdge small u v → carrierEdge big u v := by
    intro u v h
    obtain ⟨e, he, hc⟩ := (hrows u v).mp h
    obtain ⟨h1, h2⟩ := carrier_edge_mem_adj hbig (hsub e he)
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · exact h2
  refine ⟨hadj, fun p hp => ?_⟩
  obtain ⟨a, b⟩ := p
  have h := (hsmall.2.2.2.2.2.2.2 a b).mp hp
  exact (hbig.2.2.2.2.2.2.2 a b).mpr ⟨h.1, hadj a b h.2⟩

/-- **A tree valid on the live carrier is valid on the layout carrier.** The two carriers have the
same cells, and every live adjacency is a layout adjacency. -/
theorem treeValid_of_live {big small : topology.Carrier} {t : spanning_tree.Tree}
    (hcells : cellCount small = cellCount big)
    (hadj : ∀ u v, carrierEdge small u v → carrierEdge big u v)
    (ht : TreeValid small t) : TreeValid big t :=
  ⟨by rw [← hcells]; exact ht.1, ht.2.1, fun u hu hne => hadj _ _ (ht.2.2 u hu hne)⟩

/-- **The tree `Scene::new` returns is valid on the layout's carrier**, for a layout whose carrier is
valid and has one cell per layout cell (`layout_new_carrier_cells`). -/
theorem scene_new_tree {R : Type _} (treeRngInst : tree.Rng R)
    (hrng : constructorLegalRng treeRngInst) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hc : CarrierValid layout.carrier)
    (hcells : cellCount layout.carrier = layout.cells.val.length) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → TreeValid s.layout.carrier s.tree) := by
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
  refine okPost_bind (okPost_trivial _) ?_
  rintro ⟨r8, required1⟩ _
  cases r8 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok (fun s h => by simp at h)
  | Ok u =>
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
      have hlive0 : (alloc.vec.Vec.with_capacity topology.Edge
          (Slice.len (alloc.vec.Vec.deref layout.carrier.edges))).val = [] := rfl
      refine okPost_bind (scene_new_live_loop layout ({ slice := s5 } : alloc.vec.Vec Std.I32)
        _ hlive0) ?_
      intro live1 hlive1
      refine okPost_bind_eq (okPost_of_spec
        (constructor_carrier_from_edges_rows_spec (alloc.vec.Vec.len layout.cells)
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
        obtain ⟨hcv, hcount, _, hrows⟩ := hcarrier
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
          obtain ⟨hwv, _, _⟩ := hworkspace
          refine okPost_bind (okPost_of_spec (constructor_scene_dfs_spec treeRngInst
            hrng carrier (alloc.vec.Vec.deref required1) 0#usize rng work hcv hwv)) ?_
          rintro ⟨r12, rng1, val4⟩ hd
          simp only at hd
          cases r12 with
          | Err x =>
            simp only [Std.bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok]
            exact okPost_ok (fun s h => by simp at h)
          | Ok tree =>
            simp only [Std.bind_ok]
            obtain ⟨pub, hpub, _, htv, _, _⟩ :
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
            have hsub : ∀ x ∈ (alloc.vec.Vec.deref live1).val, x ∈ layout.carrier.edges.val :=
              fun x hx => ((hlive1 x).mp (by simpa [alloc.vec.Vec.deref] using hx)).1
            obtain ⟨hadj, _⟩ := carrier_sub_of_rows hc hcv _ hsub hrows
            have hcc : cellCount carrier = cellCount layout.carrier := by
              rw [hcount, hcells]
              simp [alloc.vec.Vec.len]
            have hfinal : TreeValid layout.carrier tree := treeValid_of_live hcc hadj htv
            refine okPost_bind (okPost_trivial _) ?_
            intro saved _
            refine okPost_bind (okPost_trivial _) ?_
            rintro pr6 _
            split
            · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
              refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
              refine okPost_ok (fun s hs => ?_)
              simp only [core.result.Result.Ok.injEq] at hs
              subst hs
              exact hfinal
            · exact okPost_ok (fun s h => by simp at h)

end Labyrinth
