module
public import LabyrinthCore.SceneReservationCrossing
public import LabyrinthCore.SceneShatterDrain

/-! Shatter (S6), part 2: the patch handle checks and the stage steps `hide_patch` and
`scatter_patch`.

`patch_slot(id)` rejects, in this order: an id of another epoch (`StaleEpoch`), a slot outside the
patch list (`InvalidIndex`), an idle patch or a serial that is not the patch's (`InvalidTransition`).
`hide_patch` and `scatter_patch` each check the stamp, then the handle, then that the scene is not
suspended, layout-pending or inactive (`InvalidTransition`), then the stage (`hide_patch`: `Parked`
else `Occupied`; `scatter_patch`: `Hidden` else `InvalidTransition`), and a positive duration
(`scatter_patch`). A rejection returns the scene unchanged. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

open Classical in
/-- What `patch_slot` answers for a handle. -/
noncomputable def slotVerdict (self : scene.Scene) (id : shatter.PatchId) :
    core.result.Result Std.Usize topology.Error :=
  if id.epoch ≠ self.stamp.epoch then .Err topology.Error.StaleEpoch
  else if self.patches.val.length ≤ id.slot.val then .Err topology.Error.InvalidIndex
  else if ∃ p, self.patches.val[id.slot.val]? = some p ∧
      (p.stage = shatter.Stage.Idle ∨ p.serial ≠ id.serial) then
    .Err topology.Error.InvalidTransition
  else .Ok id.slot

/-- The scene refuses stage changes: suspended, awaiting a layout, or inactive. -/
def Frozen (self : scene.Scene) : Prop :=
  self.suspended = true ∨ self.pending ≠ none ∨ self.inactive = true

theorem slotVerdict_stale (self : scene.Scene) (id : shatter.PatchId)
    (h : id.epoch ≠ self.stamp.epoch) :
    slotVerdict self id = .Err topology.Error.StaleEpoch := by
  unfold slotVerdict; simp [h]

theorem slotVerdict_index (self : scene.Scene) (id : shatter.PatchId)
    (he : id.epoch = self.stamp.epoch) (hl : self.patches.val.length ≤ id.slot.val) :
    slotVerdict self id = .Err topology.Error.InvalidIndex := by
  unfold slotVerdict; simp [he, hl]

theorem slotVerdict_bad (self : scene.Scene) (id : shatter.PatchId)
    (he : id.epoch = self.stamp.epoch) (hl : id.slot.val < self.patches.val.length)
    (p : shatter.Patch) (hp : self.patches.val[id.slot.val]? = some p)
    (hbad : p.stage = shatter.Stage.Idle ∨ p.serial ≠ id.serial) :
    slotVerdict self id = .Err topology.Error.InvalidTransition := by
  unfold slotVerdict
  have : ¬ self.patches.val.length ≤ id.slot.val := by omega
  have hex : ∃ p', self.patches.val[id.slot.val]? = some p' ∧
      (p'.stage = shatter.Stage.Idle ∨ p'.serial ≠ id.serial) := ⟨p, hp, hbad⟩
  simp only [he, ne_eq, not_true_eq_false, ↓reduceIte, this, hex]

theorem slotVerdict_ok (self : scene.Scene) (id : shatter.PatchId)
    (he : id.epoch = self.stamp.epoch) (hl : id.slot.val < self.patches.val.length)
    (p : shatter.Patch) (hp : self.patches.val[id.slot.val]? = some p)
    (hs : p.stage ≠ shatter.Stage.Idle) (hser : p.serial = id.serial) :
    slotVerdict self id = .Ok id.slot := by
  unfold slotVerdict
  have : ¬ self.patches.val.length ≤ id.slot.val := by omega
  have hex : ¬ ∃ p', self.patches.val[id.slot.val]? = some p' ∧
      (p'.stage = shatter.Stage.Idle ∨ p'.serial ≠ id.serial) := by
    rintro ⟨p', hp', hbad⟩
    rw [hp] at hp'; cases hp'
    rcases hbad with h | h
    · exact hs h
    · exact h hser
  simp only [he, ne_eq, not_true_eq_false, ↓reduceIte, this, hex]

theorem patch_slot_spec (self : scene.Scene) (id : shatter.PatchId) :
    scene.Scene.patch_slot self id ⦃ r => r = slotVerdict self id ⦄ := by
  unfold scene.Scene.patch_slot
  by_cases he : id.epoch = self.stamp.epoch
  · have hne : (id.epoch != self.stamp.epoch) = false := by simp [he]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice shatter.Patch)
        (alloc.vec.Vec.deref self.patches) id.slot = ok (self.patches.val[id.slot.val]?) := by
      simp [core.slice.Slice.get, alloc.vec.Vec.deref]
    simp only [hget, Std.bind_ok]
    cases hp : self.patches.val[id.slot.val]? with
    | none =>
      have hlen : self.patches.val.length ≤ id.slot.val := by
        by_contra h
        have := (List.getElem?_eq_getElem (l := self.patches.val) (by omega : id.slot.val <
          self.patches.val.length))
        rw [hp] at this; simp at this
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      rw [spec_ok, slotVerdict_index self id he hlen]
    | some p =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hlt : id.slot.val < self.patches.val.length :=
        (List.getElem?_eq_some_iff.mp hp).1
      unfold shatter.Patch.validate
      simp only [Aeneas.Std.bind_assoc]
      apply spec_bind (stage_eq_spec p.stage shatter.Stage.Idle)
      intro b hb
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte, Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        rw [spec_ok, slotVerdict_bad self id he hlt p hp (Or.inl (hb.mp hbt))]
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        have hni : p.stage ≠ shatter.Stage.Idle := fun h => hbt (hb.mpr h)
        by_cases hser : p.serial = id.serial
        · have hbne : (p.serial != id.serial) = false := by simp [hser]
          simp only [hbne, Bool.false_eq_true, ↓reduceIte, Std.bind_ok]
          rw [spec_ok, slotVerdict_ok self id he hlt p hp hni hser]
        · have hbne : (p.serial != id.serial) = true := by simpa using hser
          simp only [hbne, ↓reduceIte, Std.bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          rw [spec_ok, slotVerdict_bad self id he hlt p hp (Or.inr hser)]
  · have hne : (id.epoch != self.stamp.epoch) = true := by simpa using he
    simp only [hne, ↓reduceIte]
    rw [spec_ok, slotVerdict_stale self id he]

/-- A valid handle names this patch. -/
def SlotOk (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch) : Prop :=
  slotVerdict self id = .Ok id.slot ∧ self.patches.val[id.slot.val]? = some p

theorem slotVerdict_cases (self : scene.Scene) (id : shatter.PatchId) :
    (∃ e, slotVerdict self id = .Err e) ∨
      ∃ p, SlotOk self id p ∧ p.stage ≠ shatter.Stage.Idle := by
  by_cases he : id.epoch = self.stamp.epoch
  · by_cases hl : self.patches.val.length ≤ id.slot.val
    · exact Or.inl ⟨_, slotVerdict_index self id he hl⟩
    · have hlt : id.slot.val < self.patches.val.length := by omega
      obtain ⟨p, hp⟩ : ∃ p, self.patches.val[id.slot.val]? = some p :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      by_cases hbad : p.stage = shatter.Stage.Idle ∨ p.serial ≠ id.serial
      · exact Or.inl ⟨_, slotVerdict_bad self id he hlt p hp hbad⟩
      · have hs : p.stage ≠ shatter.Stage.Idle := fun h => hbad (Or.inl h)
        have hser : p.serial = id.serial := by
          by_contra h; exact hbad (Or.inr h)
        exact Or.inr ⟨p, ⟨slotVerdict_ok self id he hlt p hp hs hser, hp⟩, hs⟩
  · exact Or.inl ⟨_, slotVerdict_stale self id he⟩

/-- `patch_stage` reads the stage of a valid handle's patch, and forwards `patch_slot`'s error. -/
theorem patch_stage_spec (self : scene.Scene) (id : shatter.PatchId) :
    scene.Scene.patch_stage self id ⦃ r =>
      (∀ e, slotVerdict self id = .Err e → r = .Err e) ∧
      (∀ p, SlotOk self id p → r = .Ok p.stage) ⦄ := by
  unfold scene.Scene.patch_stage
  apply spec_bind (patch_slot_spec self id)
  intro r1 hr1
  cases r1 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    rw [spec_ok]
    refine ⟨fun e' he' => ?_, fun p hp => ?_⟩
    · rw [← hr1] at he'; cases he'; rfl
    · have h1 := hp.1; rw [← hr1] at h1; simp at h1
  | Ok v =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    rcases slotVerdict_cases self id with ⟨e, he⟩ | ⟨p, hp, _⟩
    · rw [he] at hr1; simp at hr1
    · have hv : v = id.slot := by
        rw [hp.1] at hr1; simpa using hr1.symm.symm
      subst hv
      have hl : id.slot.val < self.patches.val.length := (List.getElem?_eq_some_iff.mp hp.2).1
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec self.patches id.slot hl)
      intro p' hp'
      rw [spec_ok]
      have hpp : p' = p := by
        have := hp.2
        rw [List.getElem?_eq_getElem hl] at this
        rw [hp']; exact Option.some.inj this
      subst hpp
      refine ⟨fun e' he' => ?_, fun p'' hp'' => ?_⟩
      · rw [hp.1] at he'; simp at he'
      · have := hp''.2; rw [hp.2] at this; cases this; rfl

end Labyrinth
