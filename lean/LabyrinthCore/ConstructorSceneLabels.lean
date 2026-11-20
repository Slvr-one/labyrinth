module
public import LabyrinthCore.ConstructorContraction
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The actual dense-label loop terminates and assigns only IDs below its returned count.
Representative termination is supplied by ranked links; no successful evaluation is assumed. -/
theorem constructor_scene_labels_bounded_spec (n : Usize)
    (links components labels : alloc.vec.Vec Usize) (rank : Usize → Nat)
    (hlinks : constructorRankedLinks (alloc.vec.Vec.deref links) rank)
    (hlinksLen : links.val.length = n.val)
    (hcomponents : n.val ≤ components.val.length) (hlabels : n.val ≤ labels.val.length)
    (hempty : ∀ r : Usize, r.val < n.val → labels.val[r.val]? = some n) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop2 n links 0#usize components labels 0#usize)
      (fun output => output.1.val.length = components.val.length ∧ output.2.val ≤ n.val ∧
        (∀ j, j < n.val → ∃ value : Usize,
          output.1.val[j]? = some value ∧ value.val < output.2.val)) := by
  let invariant : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize → Prop :=
    fun state => state.1.val ≤ n.val ∧ state.2.2.2.val ≤ state.1.val ∧
      state.2.1.val.length = components.val.length ∧ state.2.2.1.val.length = labels.val.length ∧
      (∀ r : Usize, r.val < n.val → ∃ value : Usize,
        state.2.2.1.val[r.val]? = some value ∧ (value = n ∨ value.val < state.2.2.2.val)) ∧
      (∀ j, j < state.1.val → ∃ value : Usize,
        state.2.1.val[j]? = some value ∧ value.val < state.2.2.2.val)
  unfold spanning_tree.Tree.scene_dfs_loop2
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize => n.val - state.1.val)
    invariant
  · rintro ⟨index, currentComponents, currentLabels, count⟩ hi
    obtain ⟨hindex, hcount, hclen, hllen, hrange, hprefix⟩ := hi
    dsimp only at hindex hcount hclen hllen hrange hprefix
    unfold spanning_tree.Tree.scene_dfs_loop2.body
    by_cases hmore : index < n
    · have hib : index.val < n.val := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (constructor_representative_spec (alloc.vec.Vec.deref links) rank hlinks
        index (by simpa [alloc.vec.Vec.deref, hlinksLen] using hib))
      intro representative hrep
      have hrb : representative.val < n.val := by
        have hb : representative.val < links.val.length := by
          simpa [alloc.vec.Vec.deref] using hrep.1
        omega
      have hrlb : representative.val < currentLabels.val.length := by omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec currentLabels representative hrlb)
      intro oldLabel hold
      have holdLookup : currentLabels.val[representative.val]? = some oldLabel := by
        rw [List.getElem?_eq_getElem hrlb, hold]
      obtain ⟨rangeValue, hrv, hrc⟩ := hrange representative hrb
      have hrvEq : rangeValue = oldLabel := Option.some.inj (hrv.symm.trans holdLookup)
      subst rangeValue
      have hassign : WP.spec
          (if oldLabel = n then do
            let (_, back) ← currentLabels.index_mut_usize representative
            let newCount ← count + 1#usize
            ok (back count, newCount)
          else ok (currentLabels, count)) (fun state =>
            state.1.val.length = labels.val.length ∧ count.val ≤ state.2.val ∧
            state.2.val ≤ index.val + 1 ∧
            (∀ r : Usize, r.val < n.val → ∃ value : Usize,
              state.1.val[r.val]? = some value ∧ (value = n ∨ value.val < state.2.val)) ∧
            (∃ value : Usize, state.1.val[representative.val]? = some value ∧
              value.val < state.2.val)) := by
        by_cases he : oldLabel = n
        · simp only [he, ite_true]
          apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentLabels representative hrlb)
          rintro ⟨old, back⟩ ⟨_, rfl⟩
          apply WP.spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
            have hn : n.val ≤ Usize.max := by scalar_tac
            simp only [UScalar.ofNatCore_val_eq]
            omega))
          intro newCount hnc
          have hnc' : newCount.val = count.val + 1 := by simpa using hnc
          apply (WP.spec_ok _).mpr
          dsimp only
          refine ⟨by simpa using hllen, by omega, by omega, ?_, ?_⟩
          · intro r hr
            by_cases hre : r = representative
            · subst r
              exact ⟨count, by simp [alloc.vec.Vec.set, hrlb], Or.inr (by omega)⟩
            · have hrv : r.val ≠ representative.val := fun h => hre ((UScalar.eq_equiv _ _).mpr h)
              obtain ⟨value, hv, hc⟩ := hrange r hr
              refine ⟨value, ?_, ?_⟩
              · simpa [alloc.vec.Vec.set, hrv, Ne.symm hrv] using hv
              · rcases hc with heq | hlt
                · exact Or.inl heq
                · exact Or.inr (by omega)
          · exact ⟨count, by simp [alloc.vec.Vec.set, hrlb], by omega⟩
        · simp only [he, ite_false]
          apply (WP.spec_ok _).mpr
          dsimp only
          refine ⟨hllen, Nat.le_refl _, by omega, hrange, oldLabel, holdLookup, ?_⟩
          exact hrc.resolve_left he
      apply WP.spec_bind hassign
      rintro ⟨newLabels, newCount⟩ ⟨hnllen, hcountMono, hnewCount, hnewRange, value, hvalue, hvalueBound⟩
      dsimp only at hnllen hcountMono hnewCount hnewRange hvalue hvalueBound
      have hnewRepBound : representative.val < newLabels.val.length := by omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec newLabels representative hnewRepBound)
      intro actualValue hactual
      have hactualLookup : newLabels.val[representative.val]? = some actualValue := by
        rw [List.getElem?_eq_getElem hnewRepBound, hactual]
      have hactualEq : actualValue = value := Option.some.inj (hactualLookup.symm.trans hvalue)
      rw [hactualEq]
      have hcb : index.val < currentComponents.val.length := by omega
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentComponents index hcb)
      rintro ⟨oldComponent, backComponent⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hni
      have hni' : nextIndex.val = index.val + 1 := by simpa using hni
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, by omega, by simpa using hclen, hnllen, hnewRange, ?_⟩, by omega⟩
      intro j hj
      by_cases he : j = index.val
      · subst j
        exact ⟨value, by simp [alloc.vec.Vec.set, hcb], hvalueBound⟩
      · obtain ⟨oldValue, hv, hvb⟩ := hprefix j (by omega)
        refine ⟨oldValue, ?_, by omega⟩
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hv
    · have he : index.val = n.val := by
        have : ¬ index.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      dsimp only
      exact ⟨hclen, by omega, by simpa only [he] using hprefix⟩
  · refine ⟨by simp, by simp, rfl, rfl, ?_, ?_⟩
    · intro r hr
      exact ⟨n, hempty r hr, Or.inl rfl⟩
    · intro j hj
      simp at hj

end Labyrinth
