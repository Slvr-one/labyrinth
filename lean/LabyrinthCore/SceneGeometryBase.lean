module
public import LabyrinthCore.SceneGeometryGrid

/-! Geometry totality (S8), angle base. `polar::normalize` is total, and the predicates that the arc
code of `polar.rs` maintains: a validated arc has `start ∈ [0, TURN)` and `length ∈ (0, TURN]`
(`Arc::validate`); the weaker `ArcBnd` also admits the empty witness that `overlap` starts from. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

theorem turn_val : polar.TURN.val = 4096 := by simp [polar.TURN]

/-- `normalize` is the Euclidean remainder modulo `TURN`, for every `i32`. -/
@[step]
theorem polar_normalize_spec (x : Std.I32) :
    polar.normalize x ⦃ r => 0 ≤ r.val ∧ r.val < 4096 ∧ r.val = x.val % 4096 ⦄ := by
  unfold polar.normalize
  apply spec_mono (i32_rem_euclid_spec x polar.TURN (by rw [turn_val]; omega))
  intro r hr
  rw [turn_val] at hr
  omega

/-- A validated arc (`Arc::validate`): `start ∈ [0, TURN)` and `length ∈ (0, TURN]`. -/
def ArcOk (a : polar.Arc) : Prop :=
  0 ≤ a.start.val ∧ a.start.val < 4096 ∧ 0 < a.length.val ∧ a.length.val ≤ 4096

/-- An arc that may be empty. -/
def ArcBnd (a : polar.Arc) : Prop :=
  0 ≤ a.start.val ∧ a.start.val < 4096 ∧ 0 ≤ a.length.val ∧ a.length.val ≤ 4096

theorem arcOk_bnd {a : polar.Arc} (h : ArcOk a) : ArcBnd a := by
  unfold ArcOk at h; unfold ArcBnd; omega

end Labyrinth
