module
public import LabyrinthCore.SceneInvNew

/-! The scene invariant, part 10: `swept_doorway`. It writes only the scratch phase table, entry by
entry, so the table keeps its length and the scene keeps the invariant and the hold law. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The loop of `swept_doorway` keeps the scratch table's length. -/
theorem swept_doorway_loop_len (v v1 : alloc.vec.Vec Std.I32) (steps : Slice Std.I32)
    (st : core.result.Result Unit topology.Error) (i : Std.Usize) :
    OkPost (scene.Scene.swept_doorway_loop v v1 steps st i)
      (fun r => r.1.val.length = v1.val.length) := by
  unfold scene.Scene.swept_doorway_loop
  refine okPost_loop (fun s : alloc.vec.Vec Std.I32 × (core.result.Result Unit topology.Error) ×
      Std.Usize => s.1.val.length = v1.val.length)
    (fun r : alloc.vec.Vec Std.I32 × (core.result.Result Unit topology.Error) =>
      r.1.val.length = v1.val.length) _ ?_ (v1, st, i) rfl
  rintro ⟨w, s, j⟩ hw
  simp only at hw
  unfold scene.Scene.swept_doorway_loop.body
  dsimp only
  split
  · refine okPost_bind (okPost_trivial _) (fun b _ => ?_)
    split
    · refine okPost_bind (okPost_trivial _) (fun i2 _ => ?_)
      refine okPost_bind (P := fun p : alloc.vec.Vec Std.I32 ×
          (core.result.Result Unit topology.Error) => p.1.val.length = v1.val.length) ?_
        (fun p hp => okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok hp))
      split
      · exact okPost_ok hw
      · refine okPost_bind (okPost_trivial _) (fun i3 _ => ?_)
        split
        · exact okPost_ok hw
        · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
          refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
          refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
          refine okPost_bind_eq (okPost_trivial _) (fun xb hm _ => ?_)
          obtain ⟨x, back⟩ := xb
          rw [index_mut_ok_set w j x back hm]
          exact okPost_ok (by simp [hw])
    · exact okPost_ok hw
  · exact okPost_ok hw

/-- `swept_doorway` returns the scene or the scene with a new scratch table of the same length. -/
theorem swept_doorway_shape (self : scene.Scene) (edge : topology.Edge) (steps : Slice Std.I32) :
    OkPost (scene.Scene.swept_doorway self edge steps) (fun p =>
      ∃ v : alloc.vec.Vec Std.I32, v.val.length = self.next_phases.val.length ∧
        p.2 = { self with next_phases := v }) := by
  unfold scene.Scene.swept_doorway
  dsimp only
  split
  · exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
  · refine okPost_bind (swept_doorway_loop_len _ _ _ _ _) ?_
    rintro ⟨v, st⟩ hv
    simp only at hv
    repeat' (first
      | (refine okPost_ok ⟨v, hv, rfl⟩)
      | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
      | split)

/-- **`swept_doorway` keeps the scene invariant and the hold law.** -/
theorem swept_doorway_inv (self : scene.Scene) (edge : topology.Edge) (steps : Slice Std.I32)
    (h : SceneInv self ∧ HoldLaw self) :
    OkPost (scene.Scene.swept_doorway self edge steps) (fun p => SceneInv p.2 ∧ HoldLaw p.2) := by
  refine okPost_mono (swept_doorway_shape self edge steps) ?_
  rintro p ⟨v, hv, e⟩
  rw [e]
  obtain ⟨⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩, hlaw⟩ := h
  exact ⟨⟨editSafe_next hs v hv, hcap, hL, htr, hpr, hres, hcr, hroom⟩, hlaw⟩

end Labyrinth
