module
public import LabyrinthCore.ConstructorSceneInitialize
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Number of nonroot component IDs strictly below an index. -/
def constructorSceneSelectedIndex (required root index : Nat) : Nat :=
  required + index - (if root < index then 1 else 0)

/-- Actual expansion copies one original witness per nonroot component and preserves the forest prefix.
The witness hypothesis is precisely a bounded incoming slot lookup, allowing parallel quotient edges. -/
theorem constructor_scene_select_spec (work : spanning_tree.Workspace)
    (componentCount quotientRoot start : Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (selected : alloc.vec.Vec topology.Edge) (chosen : Nat → topology.Edge)
    (hroot : quotientRoot.val < componentCount.val)
    (hincoming : componentCount.val ≤ work.incoming.val.length)
    (hwitness : ∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
      ∃ slot : Usize, work.incoming.val[node.val]? = some slot ∧
        slot.val < witnesses.val.length ∧ witnesses.val[slot.val]? = some (chosen node.val))
    (hcapacity : start.val + componentCount.val - 1 ≤ selected.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop7 work 0#usize componentCount witnesses
      quotientRoot selected start) (fun output =>
      output.1 = work ∧ output.2.val.length = selected.val.length ∧
      (∀ j, j < start.val → output.2.val[j]? = selected.val[j]?) ∧
      (∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
        output.2.val[constructorSceneSelectedIndex start.val quotientRoot.val node.val]? =
          some (chosen node.val))) := by
  let invariant : spanning_tree.Workspace × Usize × alloc.vec.Vec topology.Edge × Usize → Prop :=
    fun state => state.1 = work ∧ state.2.1.val ≤ componentCount.val ∧
      state.2.2.1.val.length = selected.val.length ∧
      state.2.2.2.val = constructorSceneSelectedIndex start.val quotientRoot.val state.2.1.val ∧
      (∀ j, j < start.val → state.2.2.1.val[j]? = selected.val[j]?) ∧
      (∀ node : Usize, node.val < state.2.1.val → node ≠ quotientRoot →
        state.2.2.1.val[constructorSceneSelectedIndex start.val quotientRoot.val node.val]? =
          some (chosen node.val))
  unfold spanning_tree.Tree.scene_dfs_loop7
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize × alloc.vec.Vec topology.Edge × Usize =>
      componentCount.val - state.2.1.val) invariant
  · rintro ⟨currentWork, index, current, count⟩ hi
    obtain ⟨hwork, hindex, hlen, hcount, hprefix, hchosen⟩ := hi
    dsimp only at hwork hindex hlen hcount hprefix hchosen
    subst currentWork
    unfold spanning_tree.Tree.scene_dfs_loop7.body
    by_cases hmore : index < componentCount
    · have hib : index.val < componentCount.val := by simpa using hmore
      simp only [hmore, ite_true]
      have hstep : WP.spec
          (if index != quotientRoot then do
            let slot ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize)
              work.incoming index
            let edge ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice topology.Edge)
              witnesses slot
            let (_, back) ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice topology.Edge) current count
            let count' ← count + 1#usize
            ok (work, back edge, count')
          else ok (work, current, count)) (fun state =>
            state.1 = work ∧ state.2.1.val.length = selected.val.length ∧
            state.2.2.val = constructorSceneSelectedIndex start.val quotientRoot.val (index.val + 1) ∧
            (∀ j, j < start.val → state.2.1.val[j]? = selected.val[j]?) ∧
            (∀ node : Usize, node.val < index.val + 1 → node ≠ quotientRoot →
              state.2.1.val[constructorSceneSelectedIndex start.val quotientRoot.val node.val]? =
                some (chosen node.val))) := by
        by_cases he : index = quotientRoot
        · simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
          apply (WP.spec_ok _).mpr
          refine ⟨rfl, hlen, ?_, hprefix, ?_⟩
          · simp only [constructorSceneSelectedIndex] at hcount ⊢
            have hev : index.val = quotientRoot.val := congrArg UScalar.val he
            split at hcount <;> split <;> omega
          · intro node hn hne
            apply hchosen node _ hne
            have hnv : node.val ≠ quotientRoot.val := fun h => hne ((UScalar.eq_equiv _ _).mpr h)
            have hev : index.val = quotientRoot.val := congrArg UScalar.val he
            omega
        · simp only [bne_iff_ne, ne_eq, he, not_false_eq_true, ite_true,
            alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
          have hev : index.val ≠ quotientRoot.val := fun h => he ((UScalar.eq_equiv _ _).mpr h)
          have hcb : count.val < current.val.length := by
            unfold constructorSceneSelectedIndex at hcount
            split at hcount <;> omega
          obtain ⟨slot, hslot, hsb, hedge⟩ := hwitness index hib he
          apply WP.spec_bind (alloc.vec.Vec.index_usize_spec work.incoming index (by
            change index.val < work.incoming.val.length
            omega))
          intro actualSlot hs
          have hsl : work.incoming.val[index.val]? = some actualSlot := by
            rw [List.getElem?_eq_getElem (by omega : index.val < work.incoming.val.length), hs]
          have hse : actualSlot = slot := Option.some.inj (hsl.symm.trans hslot)
          rw [hse]
          apply WP.spec_bind (alloc.vec.Vec.index_usize_spec witnesses slot hsb)
          intro edge heLookup
          have hel : witnesses.val[slot.val]? = some edge := by
            rw [List.getElem?_eq_getElem hsb, heLookup]
          have hee : edge = chosen index.val := Option.some.inj (hel.symm.trans hedge)
          rw [hee]
          apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current count hcb)
          rintro ⟨old, back⟩ ⟨_, rfl⟩
          apply WP.spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
            have := current.property
            simp only [UScalar.ofNatCore_val_eq]
            omega))
          intro nextCount hnc
          have hnc' : nextCount.val = count.val + 1 := by simpa using hnc
          apply (WP.spec_ok _).mpr
          refine ⟨rfl, by simpa using hlen, ?_, ?_, ?_⟩
          · unfold constructorSceneSelectedIndex at hcount ⊢
            split at hcount <;> split <;> omega
          · intro j hj
            have hne : j ≠ count.val := by
              unfold constructorSceneSelectedIndex at hcount
              split at hcount <;> omega
            simpa [alloc.vec.Vec.set, hne, Ne.symm hne] using hprefix j hj
          · intro node hn hne
            by_cases hni : node = index
            · subst node
              simp only [← hcount]
              simp [alloc.vec.Vec.set, hcb]
            · have hnv : node.val ≠ index.val := fun h => hni ((UScalar.eq_equiv _ _).mpr h)
              have hnr : node.val ≠ quotientRoot.val := fun h => hne ((UScalar.eq_equiv _ _).mpr h)
              have hpos : constructorSceneSelectedIndex start.val quotientRoot.val node.val ≠ count.val := by
                unfold constructorSceneSelectedIndex at hcount ⊢
                split at hcount <;> split <;> omega
              simpa [alloc.vec.Vec.set, hpos, Ne.symm hpos] using hchosen node (by omega) hne
      apply WP.spec_bind hstep
      rintro ⟨nextWork, nextSelected, nextCount⟩ ⟨rfl, hnl, hnc, hnp, hns⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hc : componentCount.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hni
      have hni' : nextIndex.val = index.val + 1 := by simpa using hni
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨rfl, by omega, hnl, ?_, hnp, ?_⟩, by omega⟩
      · simpa only [hni'] using hnc
      · simpa only [hni'] using hns
    · have he : index.val = componentCount.val := by
        have : ¬ index.val < componentCount.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨rfl, hlen, hprefix, by simpa only [he] using hchosen⟩
  · exact ⟨rfl, by simp, rfl, by simp [constructorSceneSelectedIndex],
      fun _ _ => rfl, fun _ h => by simp at h⟩

end Labyrinth
