module
public import LabyrinthCore.SceneInvCarve

/-! The scene invariant, part 7: the shatter operations keep it and the hold law.

`begin_shatter` places a draining patch and drains; `hide_patch` hides the walkers of a parked patch;
`scatter_patch` only moves a hidden patch on; `reform_patch` is an edit inside a scattered patch.
None writes a hold counter. The sweeps of `begin_shatter` and `hide_patch` rewrite only walkers that
are not crossing (`drain_patches` parks a patch only when nothing crosses it, and a parked patch is
clear of crossings), and every stage change keeps the patch's cells. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- A scene that differs from an invariant one only in walkers that relax the old ones and in patches
with room for every cell. -/
theorem sceneInv_of_relaxed {self s' : scene.Scene} (h : SceneInv self)
    (h1 : s'.layout = self.layout) (h2 : s'.tree = self.tree) (h3 : s'.work = self.work)
    (h4 : s'.routes = self.routes) (h5 : s'.required = self.required)
    (h6 : s'.phases = self.phases) (h7 : s'.next_phases = self.next_phases)
    (h8 : s'.holds = self.holds) (hrel : RelaxedList self.walkers.val s'.walkers.val)
    (hroom : PatchRoom s') : SceneInv s' := by
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, ecap, hL, htr, hpr, hres, hcr, _⟩ := h
  have hres' : ResInv s' := by
    unfold ResInv; rw [h8]; exact resInvL_relaxed _ _ _ hres hrel.1 hrel.2
  have hcr' : CrossHeld s' := crossHeld_transfer self s' hcr hL h1 (relaxed_crossSub hrel)
    (fun _ _ _ _ _ _ hpe => by rw [h2]; exact hpe) (fun _ _ _ _ _ _ => by rw [h6])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hres', hcr', hroom⟩ <;>
    simp only [EditCapacity, PhaseRange, h1, h2, h3, h4, h5, h6, h7] <;> assumption

/-- Moving a settled patch to another stage keeps the patches clear. -/
theorem patchClear_set_stage {ws : List walker.Walker} {ps : List shatter.Patch}
    (h : PatchClearL ws ps) (p : shatter.Patch) (hp : p ∈ ps) (h1 : p.stage ≠ shatter.Stage.Idle)
    (h2 : p.stage ≠ shatter.Stage.Draining) (i : Nat) (s : shatter.Stage) :
    PatchClearL ws (ps.set i { p with stage := s }) := by
  intro q hq g1 g2 ht
  rcases List.mem_or_eq_of_mem_set hq with hq | rfl
  · exact h q hq g1 g2 ht
  · exact h p hp h1 h2 ((touches_congr ws (p := { p with stage := s }) (p' := p) rfl g1 h1).mp ht)

/-- Moving a patch to another stage keeps its room. -/
theorem patchRoom_set_stage {self : scene.Scene} (h : PatchRoom self) (p : shatter.Patch)
    (hp : p ∈ self.patches.val) (i : Nat) (s : shatter.Stage) :
    ∀ q ∈ self.patches.val.set i { p with stage := s },
      q.cells.val.length = self.layout.cells.val.length := by
  intro q hq
  rcases List.mem_or_eq_of_mem_set hq with hq | rfl
  · exact h q hq
  · exact h p hp

theorem slotOk_mem {self : scene.Scene} {id : shatter.PatchId} {p : shatter.Patch}
    (h : SlotOk self id p) : p ∈ self.patches.val := List.mem_of_getElem? h.2

/-! ### `begin_shatter` -/

/-- The scene after a successful `begin_shatter`, read off `DrainOf`. -/
theorem shattered_lists {self : scene.Scene} {slot : Std.Usize} {np : shatter.Patch}
    {cw : alloc.vec.Vec walker.Walker} {cp : alloc.vec.Vec shatter.Patch}
    (hd : DrainOf (shatterStart self slot np) cw cp) :
    cw.val = self.walkers.val.map (drainW self.walkers.val (self.patches.val.set slot.val np)
      (self.patches.val.set slot.val np).length) ∧
    cp.val = (self.patches.val.set slot.val np).map (drainP self.walkers.val) := by
  obtain ⟨hlw, hlp, hp, hw⟩ := hd
  simp only [shatterStart, alloc.vec.Vec.set_val_eq] at hlw hlp hp hw
  exact ⟨list_eq_map _ _ _ hlw hw, list_eq_map _ _ _ hlp hp⟩

theorem begin_shatter_inv (self : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
    (h : SceneInv self) :
    OkPost (scene.Scene.begin_shatter self stamp cells) (fun res => SceneInv res.2) := by
  have hcs : CrossAtSource self.walkers.val := fun wk hwk c hc => (h.2.2.2.2.2.1.1 wk hwk c hc).2.2
  intro res hres
  have hout := okPost_of_spec (begin_shatter_spec self stamp cells hcs h.2.2.2.2.2.2.2) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, ⟨_, _, e⟩ | ⟨_, ⟨_, e⟩ |
      ⟨slot, old, np, v, cw, cp, _, hold, _, _, hfresh, hdrain, e⟩⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  obtain ⟨hcw, hcp⟩ := shattered_lists hdrain
  have hrel : RelaxedList self.walkers.val cw.val := by
    rw [hcw]
    refine ⟨by simp, fun i hi => ?_⟩
    refine ⟨_, drainW self.walkers.val (self.patches.val.set slot.val np)
      (self.patches.val.set slot.val np).length self.walkers.val[i],
      List.getElem?_eq_getElem hi, by simp [hi], ?_⟩
    exact drainW_eq_or _ _ _ _
  refine sceneInv_of_relaxed h rfl rfl rfl rfl rfl rfl rfl rfl hrel ?_
  intro p hp
  have hp' : p ∈ cp.val := hp
  rw [hcp] at hp'
  obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hp'
  show (drainP self.walkers.val pq).cells.val.length = self.layout.cells.val.length
  rw [drainP_cells]
  rcases List.mem_or_eq_of_mem_set hpq with hpq | rfl
  · exact h.2.2.2.2.2.2.2 pq hpq
  · rw [hfresh.2.2.1]; exact h.2.2.2.2.2.2.2 old (List.mem_of_getElem? hold)

theorem begin_shatter_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
    (hinv : SceneInv self) (h : HoldLaw self) :
    OkPost (scene.Scene.begin_shatter self stamp cells) (fun res => HoldLaw res.2) := by
  have hcs : CrossAtSource self.walkers.val :=
    fun wk hwk c hc => (hinv.2.2.2.2.2.1.1 wk hwk c hc).2.2
  intro res hres
  have hout := okPost_of_spec (begin_shatter_spec self stamp cells hcs hinv.2.2.2.2.2.2.2) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, ⟨_, _, e⟩ | ⟨_, ⟨_, e⟩ |
      ⟨slot, old, np, v, cw, cp, _, hold, _, _, hfresh, hdrain, e⟩⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  obtain ⟨hcw, hcp⟩ := shattered_lists hdrain
  have hsame : SameCrossings self.walkers.val cw.val := by
    rw [hcw]
    exact sameCrossings_map _ _ (fun o ho => drainW_same _ _ _ hcs o ho)
  have hclear : PatchClearL self.walkers.val (self.patches.val.set slot.val np) := by
    intro q hq g1 g2 ht
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact h.2 q hq g1 g2 ht
    · exact g2 hfresh.2.1
  refine ⟨holdEqL_same h.1 hsame, ?_⟩
  show PatchClearL cw.val cp.val
  rw [hcp]
  exact drain_clear hclear (crossSub_of_same hsame)

/-! ### `hide_patch` -/

theorem sweep_list {p : shatter.Patch} {s : walker.WalkerState}
    {old new : alloc.vec.Vec walker.Walker} (h : SweepOf p s old new) :
    new.val = old.val.map (stateIf p s) := by
  apply List.ext_getElem?
  intro i
  rw [h.2 i, List.getElem?_map]

theorem hide_patch_inv (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (h : SceneInv self) :
    OkPost (scene.Scene.hide_patch self stamp id) (fun res => SceneInv res.2) := by
  intro res hres
  have hout := okPost_of_spec (hide_patch_spec self stamp id) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, e⟩ |
      ⟨_, _, v, ws, _, hsw, e⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  have hrel : RelaxedList self.walkers.val ws.val := by
    rw [sweep_list hsw]
    refine ⟨by simp, fun i hi => ?_⟩
    refine ⟨_, stateIf p walker.WalkerState.Hidden self.walkers.val[i],
      List.getElem?_eq_getElem hi, by simp [hi], ?_⟩
    unfold stateIf
    split
    · right; intro c; simp
    · left; rfl
  refine sceneInv_of_relaxed h rfl rfl rfl rfl rfl rfl rfl rfl hrel ?_
  intro q hq
  have hq' : q ∈ (alloc.vec.Vec.set self.patches id.slot
    { p with stage := shatter.Stage.Hidden }).val := hq
  rw [alloc.vec.Vec.set_val_eq] at hq'
  exact patchRoom_set_stage h.2.2.2.2.2.2.2 p (slotOk_mem hp) _ _ q hq'

theorem hide_patch_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (hinv : SceneInv self) (h : HoldLaw self) :
    OkPost (scene.Scene.hide_patch self stamp id) (fun res => HoldLaw res.2) := by
  have hcs : CrossAtSource self.walkers.val :=
    fun wk hwk c hc => (hinv.2.2.2.2.2.1.1 wk hwk c hc).2.2
  intro res hres
  have hout := okPost_of_spec (hide_patch_spec self stamp id) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, e⟩ |
      ⟨_, hpk, v, ws, _, hsw, e⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  have hmem := slotOk_mem hp
  have hst1 : p.stage ≠ shatter.Stage.Idle := by rw [hpk]; simp
  have hst2 : p.stage ≠ shatter.Stage.Draining := by rw [hpk]; simp
  have hsame : SameCrossings self.walkers.val ws.val := by
    rw [sweep_list hsw]
    exact sweep_sameCrossings _ p _ (fun c => by simp) hcs (h.2 p hmem hst1 hst2)
  refine ⟨holdEqL_same h.1 hsame, ?_⟩
  show PatchClearL ws.val (alloc.vec.Vec.set self.patches id.slot
    { p with stage := shatter.Stage.Hidden }).val
  rw [alloc.vec.Vec.set_val_eq]
  exact patchClear_crossSub (patchClear_set_stage h.2 p hmem hst1 hst2 _ _) (crossSub_of_same hsame)

/-! ### `scatter_patch` -/

theorem scatter_patch_inv (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (h : SceneInv self) :
    OkPost (scene.Scene.scatter_patch self stamp id duration) (fun res => SceneInv res.2) := by
  intro res hres
  have hout := okPost_of_spec (scatter_patch_spec self stamp id duration) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ |
      ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, v, u, _, _, e⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  refine sceneInv_of_relaxed h rfl rfl rfl rfl rfl rfl rfl rfl (relaxed_refl _) ?_
  intro q hq
  have hq' : q ∈ (alloc.vec.Vec.set self.patches id.slot
    { p with stage := shatter.Stage.Scattered u }).val := hq
  rw [alloc.vec.Vec.set_val_eq] at hq'
  exact patchRoom_set_stage h.2.2.2.2.2.2.2 p (slotOk_mem hp) _ _ q hq'

theorem scatter_patch_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (h : HoldLaw self) :
    OkPost (scene.Scene.scatter_patch self stamp id duration) (fun res => HoldLaw res.2) := by
  intro res hres
  have hout := okPost_of_spec (scatter_patch_spec self stamp id duration) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ |
      ⟨_, _, _, _, e⟩ | ⟨_, hph, _, _, v, u, _, _, e⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rw [e]
  refine ⟨h.1, ?_⟩
  show PatchClearL self.walkers.val (alloc.vec.Vec.set self.patches id.slot
    { p with stage := shatter.Stage.Scattered u }).val
  rw [alloc.vec.Vec.set_val_eq]
  exact patchClear_set_stage h.2 p (slotOk_mem hp) (by rw [hph]; simp) (by rw [hph]; simp) _ _

end Labyrinth
