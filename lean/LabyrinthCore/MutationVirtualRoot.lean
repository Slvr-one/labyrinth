module
public import LabyrinthCore.MutationWorkspace
public import Mathlib.Logic.Function.Iterate

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 def mutationVirtualParent (w : spanning_tree.Workspace) (published : Slice Usize)
    (cell : Nat) : Nat :=
  let slot := w.edit_slots.val[cell]?.getD core.num.Usize.MAX
  if slot = core.num.Usize.MAX then (published.val[cell]?.getD 0#usize).val
  else (w.parents.val[slot.val]?.getD 0#usize).val

 theorem mutation_workspace_parent_exact
    (w : spanning_tree.Workspace) (published : Slice Usize) (cell : Usize)
    (hw : WorkspaceValid w) (hc : cell.val < w.path.val.length)
    (hp : cell.val < published.val.length) :
    spanning_tree.Workspace.parent w published cell ⦃ value =>
      value.val = mutationVirtualParent w published cell.val ⦄ := by
  apply spec_mono (mutation_workspace_parent_total w published cell hw hc hp)
  rintro value ⟨slot, hslot, hmax | hactive⟩
  · have heq : slot = core.num.Usize.MAX := UScalar.eq_of_val_eq hmax.1
    simp [mutationVirtualParent, hslot, heq, hmax.2]
  · have hnot : slot ≠ core.num.Usize.MAX := by
      intro heq
      have hcount := hw.2.2.2.2.2.2.1
      have hcap := w.path.property
      have hslotMax : slot.val = Usize.max := by rw [heq]; rfl
      omega
    simp [mutationVirtualParent, hslot, hnot, hactive.2]

 def MutationVirtualRootWitness (next : Nat → Nat) (n start root : Nat) : Prop :=
  ∃ k, k < n ∧ next^[k] start = root ∧ next root = root ∧
    ∀ j, j ≤ k → next^[j] start < n

 theorem mutation_virtual_root_total
    (t : spanning_tree.Tree) (start : Usize) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : t.parents.val.length ≤ w.path.val.length) :
    spanning_tree.Tree.virtual_root t start w ⦃ result =>
      (∀ root, result = core.result.Result.Ok root →
        MutationVirtualRootWitness (mutationVirtualParent w (alloc.vec.Vec.deref t.parents))
          t.parents.val.length start.val root.val) ∧
      (result = core.result.Result.Err topology.Error.InvalidTree ↔
        ¬ ∃ root, MutationVirtualRootWitness
          (mutationVirtualParent w (alloc.vec.Vec.deref t.parents))
          t.parents.val.length start.val root) ∧
      ((∃ root, result = core.result.Result.Ok root) ∨
        result = core.result.Result.Err topology.Error.InvalidTree) ⦄ := by
  let n := t.parents.val.length
  let next := mutationVirtualParent w (alloc.vec.Vec.deref t.parents)
  let witness := MutationVirtualRootWitness next n start.val
  have hloop : spanning_tree.Tree.virtual_root_loop t w start 0#usize false ⦃ out =>
      (out.2 = true → witness out.1.val) ∧
      (out.2 = false → ¬ ∃ root, witness root) ⦄ := by
    unfold spanning_tree.Tree.virtual_root_loop
    apply loop.spec_decr_nat
      (fun state : Usize × Usize × Bool => n - state.2.1.val)
      (fun state : Usize × Usize × Bool =>
        state.2.1.val ≤ n ∧
        (state.2.2 = true → witness state.1.val) ∧
        (state.2.2 = false →
          state.1.val = next^[state.2.1.val] start.val ∧
          ∀ j, j < state.2.1.val →
            next^[j] start.val < n ∧ next (next^[j] start.val) ≠ next^[j] start.val))
      _
    · rintro ⟨cell, steps, found⟩ ⟨hsteps, hfound, hwalking⟩
      dsimp only at hsteps hfound hwalking ⊢
      have hexit : (n ≤ steps.val ∨ n ≤ cell.val) →
          (found = true → witness cell.val) ∧
          (found = false → ¬ ∃ root, witness root) := by
        intro hstop
        refine ⟨hfound, ?_⟩
        intro hf
        obtain ⟨hcell, hprefix⟩ := hwalking hf
        rintro ⟨root, k, hk, hroot, hfixed, hbound⟩
        by_cases hbefore : k < steps.val
        · exact (hprefix k hbefore).2 (by simpa [hroot] using hfixed)
        · have hle : steps.val ≤ k := by omega
          rcases hstop with hstop | hstop
          · omega
          · have hinside := hbound steps.val hle
            rw [← hcell] at hinside
            omega
      unfold spanning_tree.Tree.virtual_root_loop.body
      by_cases hltSteps : steps < alloc.vec.Vec.len t.parents
      · have hltStepsNat : steps.val < n := hltSteps
        simp only [hltSteps, ite_true]
        by_cases hltCell : cell < alloc.vec.Vec.len t.parents
        · have hltCellNat : cell.val < n := hltCell
          simp only [hltCell, ite_true]
          cases found with
          | true =>
            simpa only [ite_true, spec_ok, Bool.true_eq_false, false_implies, and_true] using
              hfound
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            obtain ⟨hcell, hprefix⟩ := hwalking rfl
            apply spec_bind (mutation_workspace_parent_exact w (alloc.vec.Vec.deref t.parents)
              cell hw (by dsimp [n] at hltCellNat; omega) hltCellNat)
            intro parent hparent
            have hparentVal : parent.val = next cell.val := hparent
            by_cases heq : parent = cell
            · simp only [heq, ite_true, bind_ok]
              apply spec_bind (Usize.add_spec (x := steps) (y := 1#usize) (by
                have := t.parents.property
                dsimp [n] at hltStepsNat
                scalar_tac))
              intro steps' hsteps'
              have hstepsVal : steps'.val = steps.val + 1 := by simpa using hsteps'
              simp only [spec_ok]
              refine ⟨⟨by omega, ?_, by simp⟩, by omega⟩
              intro _
              refine ⟨steps.val, hltStepsNat, hcell.symm, ?_, ?_⟩
              · simpa [heq] using hparentVal.symm
              · intro j hj
                by_cases hjs : j = steps.val
                · simpa [hjs, ← hcell] using hltCellNat
                · exact (hprefix j (by omega)).1
            · simp only [heq, ite_false, bind_ok]
              apply spec_bind (Usize.add_spec (x := steps) (y := 1#usize) (by
                have := t.parents.property
                dsimp [n] at hltStepsNat
                scalar_tac))
              intro steps' hsteps'
              have hstepsVal : steps'.val = steps.val + 1 := by simpa using hsteps'
              simp only [spec_ok]
              refine ⟨⟨by omega, by simp, ?_⟩, by omega⟩
              intro _
              refine ⟨?_, ?_⟩
              · rw [hstepsVal, Function.iterate_succ_apply', ← hcell]
                exact hparentVal
              · intro j hj
                by_cases hjs : j = steps.val
                · rw [hjs, ← hcell]
                  refine ⟨hltCellNat, ?_⟩
                  intro hfixed
                  apply heq
                  exact UScalar.eq_of_val_eq (hparentVal.trans hfixed)
                · exact hprefix j (by omega)
        · have hge : n ≤ cell.val := Nat.le_of_not_lt hltCell
          simpa only [hltCell, ite_false, spec_ok] using hexit (Or.inr hge)
      · have hge : n ≤ steps.val := Nat.le_of_not_lt hltSteps
        simpa only [hltSteps, ite_false, spec_ok] using hexit (Or.inl hge)
    · refine ⟨by simp, by simp, ?_⟩
      intro _
      exact ⟨rfl, by simp⟩
  unfold spanning_tree.Tree.virtual_root
  apply spec_bind hloop
  rintro ⟨cell, found⟩ ⟨hfound, hnotfound⟩
  cases found with
  | false =>
    have hnot := hnotfound rfl
    simpa [witness, next, n, hnot]
  | true =>
    have hyes := hfound rfl
    have hexists : ∃ root, witness root := ⟨cell.val, hyes⟩
    simpa [witness, next, n, hexists] using hyes

end Labyrinth
