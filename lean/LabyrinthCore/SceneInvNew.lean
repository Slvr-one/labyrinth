module
public import LabyrinthCore.SceneInvReform
public import LabyrinthCore.SceneConstruction

/-! The scene invariant, part 9: what `Scene::new` establishes.

A scene `Scene::new` returns has every walker `Ready` (none is crossing), every hold counter zero
(`vec![0; transforms]`), every patch idle with one entry per layout cell (`Patch::new(count)`), and
published and scratch phase tables of length `transforms` that are all zero after the spinning-portal
scan (`NewFacts`). Together with the layout's geometry these give every part of `SceneInv` other than
the edit preconditions `EditSafe` and `EditCapacity`, and the whole hold law. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- What a scene returned by `Scene::new layout ...` looks like, beyond `scene_new_spec`. -/
def NewFacts (layout : scene.Layout) (s : scene.Scene) : Prop :=
  s.layout = layout ∧ (∀ w ∈ s.walkers.val, w.state = walker.WalkerState.Ready) ∧
  s.holds.val = List.replicate layout.transforms.val 0#usize ∧
  (∀ p ∈ s.patches.val, p.stage = shatter.Stage.Idle ∧
    p.cells.val.length = layout.cells.val.length) ∧
  s.phases.val.length = layout.transforms.val ∧ AllZeroPhases s.phases.val ∧
  s.next_phases.val.length = layout.transforms.val

/-- The occupant loop builds only `Ready` walkers. -/
theorem new_walkers_ready (L : scene.Layout) (occupants : Slice Std.Usize) (count : Std.Usize)
    (walkers : alloc.vec.Vec walker.Walker)
    (h : ∀ w ∈ walkers.val, w.state = walker.WalkerState.Ready) :
    OkPost (scene.Scene.new_loop2 L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms occupants count walkers true 0#usize)
      (fun y => ∀ w ∈ y.1.val, w.state = walker.WalkerState.Ready) := by
  unfold scene.Scene.new_loop2
  refine okPost_loop (fun s : alloc.vec.Vec walker.Walker × Bool × Std.Usize =>
      ∀ w ∈ s.1.val, w.state = walker.WalkerState.Ready)
    (fun y : alloc.vec.Vec walker.Walker × Bool => ∀ w ∈ y.1.val, w.state = walker.WalkerState.Ready)
    _ ?_ (walkers, true, 0#usize) h
  rintro ⟨w, v, i⟩ hw
  simp only at hw
  unfold scene.Scene.new_loop2.body
  dsimp only
  split
  · split
    · refine okPost_bind (okPost_trivial _) (fun cell _ => ?_)
      refine okPost_bind (P := fun w1 : alloc.vec.Vec walker.Walker =>
        ∀ x ∈ w1.val, x.state = walker.WalkerState.Ready) ?_
        (fun w1 hw1 => okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok hw1))
      split
      · refine okPost_bind (okPost_trivial _) (fun lp _ => ?_)
        refine okPost_mono (vec_push_okPost _ _) (fun w1 hw1 x hx => ?_)
        rw [hw1, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · rfl
      · exact okPost_ok hw
    · exact okPost_ok hw
  · exact okPost_ok hw

/-- The patch loop builds idle patches with one entry per cell. -/
theorem new_patches_idle (patch_capacity count : Std.Usize) (patches : alloc.vec.Vec shatter.Patch)
    (h : ∀ p ∈ patches.val, p.stage = shatter.Stage.Idle ∧ p.cells.val.length = count.val) :
    OkPost (scene.Scene.new_loop3 patch_capacity count patches 0#usize)
      (fun y => ∀ p ∈ y.val, p.stage = shatter.Stage.Idle ∧ p.cells.val.length = count.val) := by
  unfold scene.Scene.new_loop3
  refine okPost_loop (fun s : alloc.vec.Vec shatter.Patch × Std.Usize =>
      ∀ p ∈ s.1.val, p.stage = shatter.Stage.Idle ∧ p.cells.val.length = count.val)
    (fun y : alloc.vec.Vec shatter.Patch =>
      ∀ p ∈ y.val, p.stage = shatter.Stage.Idle ∧ p.cells.val.length = count.val)
    _ ?_ (patches, 0#usize) h
  rintro ⟨ps, i⟩ hps
  simp only at hps
  unfold scene.Scene.new_loop3.body
  by_cases hlt : i < patch_capacity
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (P := fun p : shatter.Patch =>
      p.stage = shatter.Stage.Idle ∧ p.cells.val.length = count.val) ?_ ?_
    · unfold shatter.Patch.new
      refine okPost_bind (okPost_of_spec
        (alloc.vec.from_elem_spec core.clone.CloneBool false count rfl)) (fun v hv => ?_)
      refine okPost_ok ⟨rfl, ?_⟩
      show v.val.length = count.val
      rw [hv.1, List.length_replicate]
    · intro p hp
      refine okPost_bind (vec_push_okPost _ _) (fun ps1 hps1 => ?_)
      refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
      intro q hq
      rw [hps1, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hps q hq
      · exact hp
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hps

/-- **What `Scene::new` returns.** -/
theorem scene_new_facts {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → NewFacts layout s) := by
  by_cases hpass : SceneStoragePass layout routes occupants patch_capacity
  swap
  · rw [scene_new_not_pass treeRngInst layout routes occupants patch_capacity epoch rng hpass]
    exact okPost_ok (fun s h => by simp at h)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpass
  rw [scene_new_checks_pass treeRngInst layout routes occupants patch_capacity epoch rng h1 h2
    h3 h4 h5 h6 h7 h8]
  unfold sceneNewTail
  refine okPost_bind_eq (okPost_of_spec
    (alloc.vec.from_elem_spec core.clone.CloneI32 0#i32 layout.transforms rfl)) ?_
  intro phases _ hph
  have hedges : topology.Carrier.impl.edges layout.carrier =
      ok (alloc.vec.Vec.deref layout.carrier.edges) := rfl
  rw [hedges, Std.bind_ok]
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro e he _
  have hphz : AllZeroPhases phases.val := by
    intro i x hx
    rw [hph.1] at hx
    simp only [List.getElem?_replicate] at hx
    split at hx
    · simp only [Option.some.injEq] at hx; subst hx; simp
    · simp at hx
  have hphl : phases.val.length = layout.transforms.val := by rw [hph.1, List.length_replicate]
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    have hzp : AllZeroPhases phases.slice.val := hphz
    simp only [lift, Std.bind_ok, alloc.vec.Vec.deref_mut]
    refine okPost_bind_eq (layout_check_spinning_portals_post layout routes phases.slice
      phases.slice hzp hzp) ?_
    rintro ⟨r9, s5, s6⟩ _ ⟨hl5, hl6, hz5, hz6, _⟩
    simp only at hl5 hl6 hz5 hz6
    cases r9 with
    | Err x =>
      simp only [Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact okPost_ok (fun s h => by simp at h)
    | Ok u =>
      simp only [Std.bind_ok]
      have hw0 : ∀ w ∈ (alloc.vec.Vec.with_capacity walker.Walker (Slice.len occupants)).val,
          w.state = walker.WalkerState.Ready := by simp [with_capacity_val]
      have hp0 : ∀ p ∈ (alloc.vec.Vec.with_capacity shatter.Patch patch_capacity).val,
          p.stage = shatter.Stage.Idle ∧ p.cells.val.length = (alloc.vec.Vec.len layout.cells).val := by
        simp [with_capacity_val]
      repeat' (first
        | (refine okPost_ok (fun s h => ?_); simp at h; done)
        | (refine okPost_bind (okPost_residual_gen
            (P := fun r : core.result.Result scene.Scene topology.Error => ∃ e, r = .Err e) _
            (fun e => ⟨e, rfl⟩)) ?_; rintro _ ⟨_, rfl⟩)
        | (refine okPost_bind (new_walkers_ready _ _ _ _ hw0) ?_; intro wk hwk)
        | (refine okPost_bind (new_patches_idle _ _ _ hp0) ?_; intro pt hpt)
        | (refine okPost_bind (okPost_of_spec
            (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize layout.transforms rfl)) ?_;
            intro hv hhv)
        | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
        | split)
      all_goals
        refine okPost_ok (fun s hs => ?_)
        simp only [core.result.Result.Ok.injEq] at hs
        subst hs
        exact ⟨rfl, hwk, hhv.1, fun p hp => by simpa using hpt p hp, hl5.trans hphl, hz5,
          hl6.trans hphl⟩

/-- No walker of the list is crossing: nothing is held. -/
theorem crossMult_none (l : List walker.Walker)
    (h : ∀ w ∈ l, w.state = walker.WalkerState.Ready) (k : Nat) : crossMult l k = 0 := by
  unfold crossMult
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact walkerMult_notCrossing w k (fun c hc => by rw [h w hw] at hc; cases hc)

/-- **A scene `Scene::new` returns satisfies the hold law**, and every part of the scene invariant
other than the edit preconditions. -/
theorem newFacts_inv {layout : scene.Layout} {s : scene.Scene} (h : NewFacts layout s)
    (hL : LayoutGeom layout) :
    HoldLaw s ∧ LayoutGeom s.layout ∧ s.layout.transforms.val ≤ s.phases.val.length ∧
      PhaseRange s ∧ ResInv s ∧ CrossHeld s ∧ PatchRoom s := by
  obtain ⟨hlay, hready, hholds, hpat, hphl, hz, _⟩ := h
  have hnc : ∀ w ∈ s.walkers.val, ∀ c, w.state ≠ walker.WalkerState.Crossing c :=
    fun w hw c hc => by rw [hready w hw] at hc; cases hc
  have hzero : ∀ k, k < s.holds.val.length → ∃ a, s.holds.val[k]? = some a ∧ a.val = 0 := by
    intro k hk
    refine ⟨0#usize, ?_, rfl⟩
    rw [hholds] at hk ⊢
    simp [show k < layout.transforms.val by simpa using hk]
  refine ⟨⟨fun k hk => ?_, fun p hp h1 _ _ => h1 (hpat p hp).1⟩, by rw [hlay]; exact hL,
    by rw [hlay, hphl], fun x hx => ?_, ⟨fun w hw c hc => absurd hc (hnc w hw c), fun k hk => ?_⟩,
    fun w hw c hc => absurd hc (hnc w hw c), fun p hp => by rw [hlay]; exact (hpat p hp).2⟩
  · obtain ⟨a, ha, h0⟩ := hzero k hk
    exact ⟨a, ha, by rw [h0, crossMult_none _ hready]⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hz i _ (List.getElem?_eq_getElem hi)
    omega
  · obtain ⟨a, ha, h0⟩ := hzero k hk
    exact ⟨a, ha, by rw [h0, crossMult_none _ hready]⟩

/-- **`Scene::new` establishes the hold law and the scene invariant**, given the edit
preconditions of the scene it returns (`EditSafe`, `EditCapacity`). -/
theorem scene_new_inv {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hL : LayoutGeom layout) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → HoldLaw s ∧
        (EditSafe s → EditCapacity s → SceneInv s)) := by
  refine okPost_mono (scene_new_facts treeRngInst layout routes occupants patch_capacity epoch rng)
    (fun p hp s hs => ?_)
  obtain ⟨hlaw, hg, htr, hpr, hres, hcr, hroom⟩ := newFacts_inv (hp s hs) hL
  exact ⟨hlaw, fun hsafe hcap => ⟨hsafe, hcap, hg, htr, hpr, hres, hcr, hroom⟩⟩

end Labyrinth
