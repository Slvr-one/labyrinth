module
public import LabyrinthCore.SceneInvMotion

/-! The scene invariant, part 5: edits keep it, and `motion` keeps it on every outcome.

`sceneInv_of_edit` is what every edit operation (`motion`, `carve`, `reform_patch`) uses: a safe
scene on the same layout, walkers and holds, with the same workspace capacity, whose published
phases stay in range and keep every held transform's phase, and whose tree keeps every crossing
walker's edge, satisfies the invariant again. An accepted edit keeps a crossing walker's edge because
it removes none (`avoids_kept`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- `Edge::new` on either orientation of an edge's ends returns that edge. -/
theorem edge_new_of_ends {a b : Std.Usize} {e1 e : topology.Edge}
    (h : topology.Edge.new a b = ok e1)
    (he : (e.u.val = e1.u.val ∧ e.v.val = e1.v.val) ∨ (e.v.val = e1.u.val ∧ e.u.val = e1.v.val)) :
    topology.Edge.new e.u e.v = ok e1 := by
  have hle : e1.u.val ≤ e1.v.val := by
    unfold topology.Edge.new at h
    split at h <;> simp only [ok.injEq] at h <;> subst h <;> scalar_tac
  obtain ⟨u1, v1⟩ := e1
  obtain ⟨u, v⟩ := e
  simp only at hle he
  unfold topology.Edge.new
  split <;> simp only [ok.injEq, topology.Edge.mk.injEq] <;>
    exact ⟨UScalar.eq_of_val_eq (by scalar_tac), UScalar.eq_of_val_eq (by scalar_tac)⟩

/-- An edit that avoids the crossings does not remove a crossing walker's edge. -/
theorem avoids_kept {self : scene.Scene} {remove : Slice topology.Edge}
    (h : AvoidsCrossings self remove) (wk : walker.Walker) (hw : wk ∈ self.walkers.val)
    (c : walker.Crossing) (hc : wk.state = walker.WalkerState.Crossing c) (e1 : topology.Edge)
    (he : topology.Edge.new c.source c.target = ok e1) :
    ¬ mutationRemoval remove e1.u.val e1.v.val := by
  rintro ⟨e, hmem, hends⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  exact h wk hw c hc e1 he j e hj (edge_new_of_ends he hends)

/-- A crossing walker's edge survives an accepted edit that avoids the crossings. -/
theorem edited_keeps_crossings {self : scene.Scene} {edit : scene.Edit} {t : spanning_tree.Tree}
    (hedt : ∀ u v, parentEdge (parents t) u v ↔
      MutationEditedEdge (parents self.tree) edit.remove edit.add u v)
    (hav : AvoidsCrossings self edit.remove) :
    ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ e1 : topology.Edge, topology.Edge.new c.source c.target = ok e1 →
      parentEdge (parents self.tree) e1.u.val e1.v.val →
      parentEdge (parents t) e1.u.val e1.v.val :=
  fun wk hw c hc e1 he hpe => (hedt _ _).mpr (Or.inl ⟨hpe, avoids_kept hav wk hw c hc e1 he⟩)

/-- Published phases given index by index, all in range. -/
theorem phaseRange_of_index {s : scene.Scene}
    (h : ∀ j, j < s.phases.val.length → ∃ n, s.phases.val[j]? = some n ∧ 0 ≤ n.val ∧ n.val < 4096) :
    PhaseRange s := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
  obtain ⟨n, hn, h0, h1⟩ := h j hj
  rw [List.getElem?_eq_getElem hj, hxj] at hn
  cases hn
  exact ⟨h0, h1⟩

/-- **Edits keep the invariant.** -/
theorem sceneInv_of_edit {self s' : scene.Scene} (h : SceneInv self) (hs' : EditSafe s')
    (hw : s'.walkers = self.walkers) (hh : s'.holds = self.holds) (hroom : PatchRoom s')
    (hlay : s'.layout = self.layout) (hwc : s'.work.edge_capacity = self.work.edge_capacity)
    (hphl : s'.phases.val.length = self.phases.val.length)
    (hrange : ∀ j, j < s'.phases.val.length →
      ∃ n, s'.phases.val[j]? = some n ∧ 0 ≤ n.val ∧ n.val < 4096)
    (hheld : ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ x ∈ c.holds.ids.val.take c.holds.count.val,
        self.phases.val[x.val]? = s'.phases.val[x.val]?)
    (htree : ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ e1 : topology.Edge, topology.Edge.new c.source c.target = ok e1 →
      parentEdge (parents self.tree) e1.u.val e1.v.val →
      parentEdge (parents s'.tree) e1.u.val e1.v.val) :
    SceneInv s' := by
  obtain ⟨_, hcap, hL, htr, _, hres, hcr, _⟩ := h
  refine ⟨hs', ?_, ?_, ?_, phaseRange_of_index hrange, ?_,
    crossHeld_transfer self s' hcr hL hlay (by rw [hw]; exact crossSub_refl _) htree hheld, hroom⟩
  · unfold EditCapacity; rw [hlay, hwc]; exact hcap
  · rw [hlay]; exact hL
  · rw [hlay, hphl]; exact htr
  · unfold ResInv; rw [hw, hh]; exact hres

/-- Phases left in place keep every held phase and stay in range. -/
theorem same_phases_range {self s' : scene.Scene} (hpr : PhaseRange self)
    (hph : s'.phases = self.phases) :
    ∀ j, j < s'.phases.val.length → ∃ n, s'.phases.val[j]? = some n ∧ 0 ≤ n.val ∧ n.val < 4096 := by
  intro j hj
  refine ⟨s'.phases.val[j], List.getElem?_eq_getElem hj, ?_⟩
  have := hpr _ (by rw [← hph]; exact List.getElem_mem hj)
  exact this

/-- The published phases after an accepted motion that published the scratch table: in range. -/
theorem motion_phases_range {self s' : scene.Scene} {steps : Slice Std.I32}
    {np : alloc.vec.Vec Std.I32} (hacc : PrepAccepted self steps np)
    (hphl : s'.phases.val.length = self.phases.val.length)
    (hnp : ∀ j, j < self.phases.val.length → s'.phases.val[j]? = np.val[j]?) :
    ∀ j, j < s'.phases.val.length → ∃ n, s'.phases.val[j]? = some n ∧ 0 ≤ n.val ∧ n.val < 4096 := by
  intro j hj
  rw [hphl] at hj
  rw [hnp j hj]
  exact prepAccepted_range hacc j hj

/-- ... and they keep the phase of every transform a crossing holds. -/
theorem motion_phases_held {self s' : scene.Scene} {steps : Slice Std.I32}
    {np : alloc.vec.Vec Std.I32} (hacc : PrepAccepted self steps np) (hpr : PhaseRange self)
    (hres : ResInv self) (hphl : s'.phases.val.length = self.phases.val.length)
    (hnp : ∀ j, j < self.phases.val.length → s'.phases.val[j]? = np.val[j]?) :
    ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ x ∈ c.holds.ids.val.take c.holds.count.val,
        self.phases.val[x.val]? = s'.phases.val[x.val]? := by
  intro wk hwk c hc x hx
  by_cases hxl : x.val < self.phases.val.length
  · rw [hnp x.val hxl]
    obtain ⟨a, ha, ha1⟩ := resInv_held_positive self hres wk hwk c hc x hx
    exact (prepAccepted_held hacc hpr x.val a ha (by omega) hxl).symm
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **`motion` keeps the scene invariant**, whatever it returns. -/
theorem motion_inv (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (h : SceneInv self) :
    OkPost (scene.Scene.motion self stamp steps edit) (fun p => SceneInv p.2) := by
  have h' := h
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h'
  intro p hp
  obtain ⟨hs', herr, hok⟩ := scene_motion_spec self stamp steps edit hs hcap p hp
  obtain ⟨hw, hh, hpa, hlay, hwc, hphl, hacc⟩ := motion_shape self stamp steps edit hs p hp
  have hav := motion_safe self stamp steps edit hs hL htr (crossHeld_fresh hcr) p hp
  have hroom' : PatchRoom p.2 := by unfold PatchRoom; rw [hpa, hlay]; exact hroom
  cases hr : p.1 with
  | Err x =>
    obtain ⟨req, np, wk, he⟩ := herr x hr
    have hph : p.2.phases = self.phases := by rw [he]
    refine sceneInv_of_edit h hs' hw hh hroom' hlay hwc hphl (same_phases_range hpr hph)
      (fun _ _ _ _ _ _ => by rw [hph]) (fun _ _ _ _ _ _ hpe => by rw [he]; exact hpe)
  | Ok ev =>
    obtain ⟨_, _, hedt, _, _⟩ := hok ev hr
    have htree := edited_keeps_crossings hedt (hav ⟨ev, hr⟩)
    obtain ⟨np, hpa', hph, _⟩ := hacc ev hr
    rcases hph with hph | hnp
    · exact sceneInv_of_edit h hs' hw hh hroom' hlay hwc hphl (same_phases_range hpr hph)
        (fun _ _ _ _ _ _ => by rw [hph]) htree
    · exact sceneInv_of_edit h hs' hw hh hroom' hlay hwc hphl
        (motion_phases_range hpa' hphl hnp) (motion_phases_held hpa' hpr hres hphl hnp) htree

end Labyrinth
