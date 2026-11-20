module
public import LabyrinthCore.ConstructorSceneLabelInvariant
public import LabyrinthCore.ConstructorSceneJoin
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The actual dense-label phase returns every class exactly once in its ID image, and identifies
vertices precisely when their union-find representatives agree. -/
theorem constructor_scene_labels_exact_spec (n : Usize)
    (links components labels : alloc.vec.Vec Usize) (rank : Usize → Nat)
    (component : Usize → Usize)
    (hrank : constructorRankedLinks links.slice rank)
    (hlabel : constructorComponentLabels links.slice component)
    (hlinks : links.val.length = n.val)
    (hc : n.val ≤ components.val.length) (hl : n.val ≤ labels.val.length)
    (hempty : ∀ r : Usize, r.val < n.val → labels.val[r.val]? = some n) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop2 n links 0#usize components labels 0#usize)
      (fun output => output.1.val.length = components.val.length ∧ output.2.val ≤ n.val ∧
        (∀ node : Usize, node.val < n.val → ∃ value : Usize,
          output.1.val[node.val]? = some value ∧ value.val < output.2.val) ∧
        (∀ value : Usize, value.val < output.2.val → ∃ node : Usize,
          node.val < n.val ∧ output.1.val[node.val]? = some value) ∧
        ∀ u v : Usize, u.val < n.val → v.val < n.val →
          (output.1.val[u.val]? = output.1.val[v.val]? ↔ component u = component v)) := by
  let invariant : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize → Prop :=
    fun state => state.2.1.val.length = components.val.length ∧
      state.2.2.1.val.length = labels.val.length ∧
      ConstructorSceneLabelsExact n component state.1.val state.2.1 state.2.2.1 state.2.2.2
  have hroot : ∀ node : Usize, node.val < n.val → (component node).val < n.val := by
    intro node hn
    have hslice : links.slice.val.length = n.val := by
      simpa only [alloc.vec.Vec.val] using hlinks
    have hp := constructor_component_root_properties links.slice rank component hrank hlabel node
      (by rw [hslice]; exact hn)
    simpa only [hslice] using hp.1
  unfold spanning_tree.Tree.scene_dfs_loop2
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize => n.val - state.1.val)
    invariant
  · rintro ⟨index, currentComponents, currentLabels, count⟩ hi
    obtain ⟨hclen, hllen, hstate⟩ := hi
    dsimp only at hclen hllen hstate
    have hindex := hstate.prefix_le
    have hcount := hstate.count_le
    unfold spanning_tree.Tree.scene_dfs_loop2.body
    by_cases hmore : index < n
    · have hib : index.val < n.val := by simpa using hmore
      have hcb : index.val < currentComponents.val.length := by omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (constructor_representative_component_spec (alloc.vec.Vec.deref links)
        rank component (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val] using hrank)
        (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val] using hlabel)
        index (by simpa [alloc.vec.Vec.deref, hlinks] using hib))
      intro representative hrep
      rw [hrep.1]
      have hrb : (component index).val < currentLabels.val.length := by
        have := hroot index hib
        omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec currentLabels (component index) hrb)
      intro oldLabel hold
      have holdLookup : currentLabels.val[(component index).val]? = some oldLabel := by
        rw [List.getElem?_eq_getElem hrb, hold]
      have hassign : WP.spec
          (if oldLabel = n then do
            let (_, back) ← currentLabels.index_mut_usize (component index)
            let nextCount ← count + 1#usize
            ok (back count, nextCount)
          else ok (currentLabels, count)) (fun state =>
            state.1.val.length = labels.val.length ∧ count.val ≤ state.2.val ∧
            ∃ value : Usize, state.1.val[(component index).val]? = some value ∧
              ConstructorSceneLabelsExact n component (index.val + 1)
                (currentComponents.set index value) state.1 state.2) := by
        by_cases he : oldLabel = n
        · simp only [he, ite_true]
          apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentLabels (component index) hrb)
          rintro ⟨old, back⟩ ⟨_, rfl⟩
          apply WP.spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
            have hn : n.val ≤ Usize.max := by scalar_tac
            simp only [UScalar.ofNatCore_val_eq]
            omega))
          intro nextCount hn
          have hn' : nextCount.val = count.val + 1 := by simpa using hn
          apply (WP.spec_ok _).mpr
          dsimp only
          refine ⟨by simpa using hllen, by omega, count,
            by simp [alloc.vec.Vec.set, hrb], ?_⟩
          exact constructor_scene_labels_exact_fresh n index count nextCount component
            currentComponents currentLabels hstate hib hcb hrb
            (by simpa only [he] using holdLookup) hn'
        · simp only [he, ite_false]
          obtain ⟨value, hv, hvr⟩ := hstate.range (component index) (hroot index hib)
          have heq : value = oldLabel := Option.some.inj (hv.symm.trans holdLookup)
          have hvb : oldLabel.val < count.val := by
            rcases hvr with hsentinel | hbound
            · exact False.elim (he (heq.symm.trans hsentinel))
            · simpa only [heq] using hbound
          apply (WP.spec_ok _).mpr
          dsimp only
          exact ⟨hllen, Nat.le_refl _, oldLabel, holdLookup,
            constructor_scene_labels_exact_existing n index count oldLabel component
              currentComponents currentLabels hstate hib hcb holdLookup hvb⟩
      apply WP.spec_bind hassign
      rintro ⟨newLabels, newCount⟩ ⟨hnllen, hmono, value, hv, hexact⟩
      dsimp only at hnllen hmono hv hexact
      have hnewBound : (component index).val < newLabels.val.length := by
        have := hroot index hib
        omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec newLabels (component index) hnewBound)
      intro actualValue hactual
      have hactualLookup : newLabels.val[(component index).val]? = some actualValue := by
        rw [List.getElem?_eq_getElem hnewBound, hactual]
      have hactualEq : actualValue = value := Option.some.inj (hactualLookup.symm.trans hv)
      rw [hactualEq]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentComponents index hcb)
      rintro ⟨old, back⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hn
      have hn' : nextIndex.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      exact ⟨⟨by simpa using hclen, hnllen, by simpa only [hn'] using hexact⟩, by omega⟩
    · have he : index.val = n.val := by
        have : ¬ index.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      dsimp only
      refine ⟨hclen, by omega, ?_, ?_, ?_⟩
      · intro node hn
        obtain ⟨value, hv, _, hb⟩ := hstate.assigned node (by omega)
        exact ⟨value, hv, hb⟩
      · intro value hv
        obtain ⟨node, hn, hc⟩ := hstate.dense value hv
        exact ⟨node, by omega, hc⟩
      · intro u v hu hv
        exact constructor_scene_labels_exact_partition n count component currentComponents currentLabels
          (by simpa only [he] using hstate) hroot u v hu hv
  · exact ⟨rfl, rfl, constructor_scene_labels_exact_initial n component components labels hempty⟩

end Labyrinth
