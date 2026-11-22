module
public import LabyrinthCore.SceneRouteBudget

/-! Scene construction (S2), part 4a: the occupant loop of `Scene::new`. It reports `valid` exactly
when every occupant names a cell (`cell < count`); the walkers it builds along the way come from
`Layout::local_pose`, whose geometry is not shown to be total here, so the statement is partial
correctness (`OkPost`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every occupant names a cell. -/
def OccupantsValid (occupants : Slice Std.Usize) (count : Std.Usize) : Prop :=
  ∀ o ∈ occupants.val, o.val < count.val

def OccLoopInv (occupants : Slice Std.Usize) (count : Std.Usize)
    (s : (alloc.vec.Vec walker.Walker) × Bool × Std.Usize) : Prop :=
  s.2.2.val ≤ occupants.val.length ∧
  (s.2.1 = true → ∀ j, j < s.2.2.val → ∀ o, occupants.val[j]? = some o → o.val < count.val) ∧
  (s.2.1 = false → ¬ OccupantsValid occupants count)

theorem scene_new_occupant_loop_body (L : scene.Layout) (occupants : Slice Std.Usize)
    (count : Std.Usize) (walkers : alloc.vec.Vec walker.Walker) (valid : Bool) (i : Std.Usize)
    (hinv : OccLoopInv occupants count (walkers, valid, i)) :
    OkPost (scene.Scene.new_loop2.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms occupants count walkers valid i)
      (fun y => match y with
        | .cont s => OccLoopInv occupants count s
        | .done y => (y.2 = true ↔ OccupantsValid occupants count)) := by
  obtain ⟨hi, hvalid, hinvalid⟩ := hinv
  simp only at hi hvalid hinvalid
  unfold scene.Scene.new_loop2.body
  by_cases hlt : i < Slice.len occupants
  · simp only [hlt, ↓reduceIte]
    have hlt' : i.val < occupants.val.length := by simpa using hlt
    by_cases hv : valid = true
    · simp only [hv, ↓reduceIte]
      refine okPost_bind_eq (okPost_of_spec (Slice.index_usize_spec occupants i hlt')) ?_
      intro cell _ hcell
      have hcellv : occupants.val[i.val]? = some cell := by
        rw [List.getElem?_eq_getElem hlt', hcell]
      have hcellv2 : occupants.val[i.val]? = some cell := hcellv
      refine okPost_bind (okPost_trivial _) ?_
      intro walkers1 _
      refine okPost_bind (okPost_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by
        have := occupants.property
        simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) ?_
      intro i3 hi3
      have hi3v : i3.val = i.val + 1 := by simpa using hi3
      refine okPost_ok ⟨by simp only [hi3v]; omega, ?_, ?_⟩
      · intro hc j hj o ho
        have hc' : cell.val < count.val := by simpa [UScalar.lt_equiv] using hc
        show _ 
        rw [hi3v] at hj
        by_cases hji : j = i.val
        · subst hji
          rw [hcellv2] at ho
          simp only [Option.some.injEq] at ho
          subst ho; exact hc'
        · exact hvalid hv j (by omega) o ho
      · intro hc hall
        have hc' : ¬ cell.val < count.val := by simpa [UScalar.lt_equiv] using hc
        exact hc' (hall cell (List.mem_of_getElem? hcellv2))
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      have hvf : valid = false := by simpa using hv
      refine okPost_ok ?_
      show (false = true ↔ _)
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd h (hinvalid hvf)
  · simp only [hlt, ↓reduceIte]
    have hn : i.val = occupants.val.length := by
      have : ¬ i.val < occupants.val.length := by simpa using hlt
      omega
    refine okPost_ok ?_
    show (valid = true ↔ _)
    constructor
    · intro h o ho
      obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem ho
      exact hvalid h j (by omega) o (by rw [List.getElem?_eq_getElem hj, hjo])
    · intro h
      by_cases hv : valid = true
      · exact hv
      · exact absurd h (hinvalid (by simpa using hv))

/-- The occupant loop reports `valid` exactly when every occupant names a cell, starting from
`valid = true`. -/
theorem scene_new_occupant_loop (L : scene.Layout) (occupants : Slice Std.Usize)
    (count : Std.Usize) (walkers : alloc.vec.Vec walker.Walker) :
    OkPost (scene.Scene.new_loop2 L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms occupants count walkers true 0#usize)
      (fun y => y.2 = true ↔ OccupantsValid occupants count) := by
  unfold scene.Scene.new_loop2
  refine okPost_loop (OccLoopInv occupants count)
    (fun y : (alloc.vec.Vec walker.Walker) × Bool => y.2 = true ↔ OccupantsValid occupants count)
    _ ?_ (walkers, true, 0#usize) ⟨by simp, by simp, by simp⟩
  rintro ⟨w, v, i⟩ h
  dsimp only
  refine okPost_mono (scene_new_occupant_loop_body L occupants count w v i h) ?_
  intro y hy
  cases y <;> exact hy

end Labyrinth
