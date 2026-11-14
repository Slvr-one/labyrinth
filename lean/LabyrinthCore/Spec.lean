import LabyrinthCore.Types
import LabyrinthCore.Funs
open Aeneas Aeneas.Std Result labyrinth_core

/-- Partial correctness of the extracted `tree::set_parent`: whenever it returns,
success updates exactly `parents[child]` to `new_parent` (with both indices in range),
and every error leaves the parent storage unchanged. Totality (no panic, termination
of the `reaches` loop) is deliberately not claimed here. -/
theorem set_parent_spec
    (parents : Slice Std.Usize) (child new_parent : Std.Usize)
    (r : core.result.Result Unit tree.Error) (parents' : Slice Std.Usize)
    (h : tree.set_parent parents child new_parent = ok (r, parents')) :
    (r = core.result.Result.Ok () →
      child.val < parents.val.length ∧ new_parent.val < parents.val.length ∧
      parents'.val = parents.val.set child.val new_parent) ∧
    (∀ e, r = core.result.Result.Err e → parents' = parents) := by
  unfold tree.set_parent at h
  dsimp only at h
  split at h
  · simp_all
    rcases h with ⟨rfl, rfl⟩
    simp
  · split at h
    · simp_all
      rcases h with ⟨rfl, rfl⟩
      simp
    · split at h
      · simp_all
        rcases h with ⟨rfl, rfl⟩
        simp
      · cases hr : tree.reaches parents child new_parent <;> simp_all [Slice.update]
        split at h <;> simp_all <;> (rcases h with ⟨rfl, rfl⟩; simp_all)
