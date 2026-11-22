module
public import LabyrinthCore.ConstructorSceneInitialize
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Quotient fill cursors are copied from row starts, retaining all parallel witness slots. -/
theorem constructor_quotient_cursor_spec (componentCount : Usize)
    (offsets next : alloc.vec.Vec Usize)
    (hoffsets : componentCount.val ≤ offsets.val.length)
    (hnext : componentCount.val ≤ next.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop4 0#usize componentCount offsets next)
      (fun output => output.val.length = next.val.length ∧
        (∀ j, j < componentCount.val → output.val[j]? = offsets.val[j]?) ∧
        (∀ j, componentCount.val ≤ j → output.val[j]? = next.val[j]?)) := by
  let invariant : Usize × alloc.vec.Vec Usize → Prop := fun state =>
    state.1.val ≤ componentCount.val ∧ state.2.val.length = next.val.length ∧
    (∀ j, j < state.1.val → state.2.val[j]? = offsets.val[j]?) ∧
    (∀ j, state.1.val ≤ j → state.2.val[j]? = next.val[j]?)
  unfold spanning_tree.Tree.scene_dfs_loop4
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize => componentCount.val - state.1.val) invariant
  · rintro ⟨index, current⟩ hi
    obtain ⟨hindex, hlen, hprefix, hsuffix⟩ := hi
    dsimp only at hindex hlen hprefix hsuffix
    unfold spanning_tree.Tree.scene_dfs_loop4.body
    by_cases hmore : index < componentCount
    · have hib : index.val < componentCount.val := by simpa using hmore
      have hob : index.val < offsets.val.length := by omega
      have hcb : index.val < current.val.length := by omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets index hob)
      intro value hv
      have hlookup : offsets.val[index.val]? = some value := by
        rw [List.getElem?_eq_getElem hob, hv]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current index hcb)
      rintro ⟨old, back⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hc : componentCount.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hni
      have hni' : nextIndex.val = index.val + 1 := by simpa using hni
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, by simpa using hlen, ?_, ?_⟩, by omega⟩
      · intro j hj
        by_cases he : j = index.val
        · subst j
          simpa [alloc.vec.Vec.set, hcb] using hlookup.symm
        · simpa [alloc.vec.Vec.set, he, Ne.symm he] using hprefix j (by omega)
      · intro j hj
        have he : j ≠ index.val := by omega
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hsuffix j (by omega)
    · have he : index.val = componentCount.val := by
        have : ¬ index.val < componentCount.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hlen, by simpa only [he] using hprefix, by simpa only [he] using hsuffix⟩
  · exact ⟨by simp, rfl, fun _ h => by simp at h, fun _ _ => rfl⟩

end Labyrinth
