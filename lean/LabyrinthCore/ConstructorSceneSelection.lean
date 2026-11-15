module
public import LabyrinthCore.ConstructorSceneInitialize
public import LabyrinthCore.ConstructorSceneComponents
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Number of nonroot component IDs strictly below an index. -/
def constructorSceneSelectedIndex (required root index : Nat) : Nat :=
  required + index - (if root < index then 1 else 0)
/-- Original edge stored at the incoming slot selected by quotient DFS, with a total fallback
outside the proved nonroot component range. -/
def constructorSceneChosenWitness (work : spanning_tree.Workspace)
    (witnesses : alloc.vec.Vec topology.Edge) (node : Nat) : topology.Edge :=
  let fallback : topology.Edge := { u := 0#usize, v := 0#usize }
  match work.incoming.val[node]? with
  | some slot => (witnesses.val[slot.val]?).getD fallback
  | none => fallback

theorem constructor_scene_chosen_witness_eq (work : spanning_tree.Workspace)
    (witnesses : alloc.vec.Vec topology.Edge) (node : Nat)
    (slot : Usize) (edge : topology.Edge)
    (hincoming : work.incoming.val[node]? = some slot)
    (hwitness : witnesses.val[slot.val]? = some edge) :
    constructorSceneChosenWitness work witnesses node = edge := by
  simp [constructorSceneChosenWitness, hincoming, hwitness]


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
          dsimp only
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


/-- Every slot after the required prefix and before the final selection count belongs to one
nonroot component. -/
theorem constructor_scene_selected_index_surjective (start root count slot : Nat)
    (hroot : root < count) (hstart : start ≤ slot)
    (hstop : slot < start + count - 1) :
    ∃ index, index < count ∧ index ≠ root ∧
      constructorSceneSelectedIndex start root index = slot := by
  by_cases hbefore : slot < start + root
  · refine ⟨slot - start, by omega, by omega, ?_⟩
    unfold constructorSceneSelectedIndex
    split <;> omega
  · refine ⟨slot - start + 1, by omega, by omega, ?_⟩
    unfold constructorSceneSelectedIndex
    split <;> omega

/-- The two actual selection loops fill exactly the required prefix followed by one retained
original witness for every nonroot quotient component. The cardinality equation rules out
uninitialized tail entries in the allocated `n - 1` vector. -/
theorem constructor_scene_selected_actual_spec (work : spanning_tree.Workspace)
    (required : Slice topology.Edge) (componentCount quotientRoot : Usize)
    (witnesses : alloc.vec.Vec topology.Edge) (selected : alloc.vec.Vec topology.Edge)
    (chosen : Nat → topology.Edge)
    (hroot : quotientRoot.val < componentCount.val)
    (hincoming : componentCount.val ≤ work.incoming.val.length)
    (hwitness : ∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
      ∃ slot : Usize, work.incoming.val[node.val]? = some slot ∧
        slot.val < witnesses.val.length ∧ witnesses.val[slot.val]? = some (chosen node.val))
    (hcardinality :
      required.val.length + componentCount.val - 1 = selected.val.length) :
    WP.spec (do
      let selected1 ← spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected
      spanning_tree.Tree.scene_dfs_loop7 work 0#usize componentCount witnesses
        quotientRoot selected1 (Slice.len required)) (fun output =>
      output.1 = work ∧ output.2.val.length = selected.val.length ∧
      ∀ slot, slot < output.2.val.length →
        (slot < required.val.length ∧
          output.2.val[slot]? =
            (required.val[slot]?).map constructorCanonicalEdge) ∨
        ∃ node, node < componentCount.val ∧ node ≠ quotientRoot.val ∧
          slot = constructorSceneSelectedIndex required.val.length quotientRoot.val node ∧
          output.2.val[slot]? = some (chosen node)) := by
  have hcopyCapacity : required.val.length ≤ selected.val.length := by omega
  apply WP.spec_bind
    (constructor_scene_required_copy_spec required selected hcopyCapacity)
  intro copied hcopy
  have hselectCapacity :
      (Slice.len required).val + componentCount.val - 1 ≤ copied.val.length := by
    simpa only [Slice.len_val, hcopy.1] using hcardinality.le
  apply WP.spec_mono
    (constructor_scene_select_spec work componentCount quotientRoot (Slice.len required)
      witnesses copied chosen hroot hincoming hwitness hselectCapacity)
  intro output hout
  obtain ⟨hwork, hlength, hprefix, hchosen⟩ := hout
  have hfinalLength : output.2.val.length = selected.val.length :=
    hlength.trans hcopy.1
  refine ⟨hwork, hfinalLength, ?_⟩
  intro slot hslot
  by_cases hrequired : slot < required.val.length
  · exact Or.inl ⟨hrequired,
      (hprefix slot (by simpa only [Slice.len_val] using hrequired)).trans
        (hcopy.2.1 slot hrequired)⟩
  · have hstart : required.val.length ≤ slot := by omega
    have hstop : slot < required.val.length + componentCount.val - 1 := by
      rw [hcardinality]
      simpa only [hfinalLength] using hslot
    obtain ⟨node, hnode, hnonroot, hindex⟩ :=
      constructor_scene_selected_index_surjective required.val.length quotientRoot.val
        componentCount.val slot hroot hstart hstop
    have hwidth : node < 2 ^ UScalarTy.Usize.numBits :=
      lt_trans hnode componentCount.hBounds
    let actualNode : Usize := UScalar.ofNatCore node hwidth
    have hactualNode : actualNode.val = node := by
      simp only [actualNode, UScalar.ofNatCore_val_eq]
    have hactualNonroot : actualNode ≠ quotientRoot := by
      intro he
      exact hnonroot (by simpa only [hactualNode] using congrArg UScalar.val he)
    have hselected := hchosen actualNode (by simpa only [hactualNode] using hnode)
      hactualNonroot
    exact Or.inr ⟨node, hnode, hnonroot, hindex.symm,
      by simpa only [Slice.len_val, hactualNode, hindex] using hselected⟩

/-- The actual forest and dense-label outputs discharge the selection size equation; callers do
not assume a final selected-edge cardinality. -/
theorem constructor_scene_selected_from_outputs_spec (work : spanning_tree.Workspace)
    (n : Usize) (required : Slice topology.Edge) (links : alloc.vec.Vec Usize)
    (componentCount quotientRoot : Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (selected : alloc.vec.Vec topology.Edge) (chosen : Nat → topology.Edge)
    (hroot : quotientRoot.val < componentCount.val)
    (hincoming : componentCount.val ≤ work.incoming.val.length)
    (hwitness : ∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
      ∃ slot : Usize, work.incoming.val[node.val]? = some slot ∧
        slot.val < witnesses.val.length ∧ witnesses.val[slot.val]? = some (chosen node.val))
    (hforestCount :
      required.val.length + constructorSceneRootCount links = n.val)
    (hcomponentCount :
      componentCount.val = constructorSceneRootCount links)
    (hselectedLength : selected.val.length = n.val - 1) :
    WP.spec (do
      let selected1 ← spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected
      spanning_tree.Tree.scene_dfs_loop7 work 0#usize componentCount witnesses
        quotientRoot selected1 (Slice.len required)) (fun output =>
      output.1 = work ∧ output.2.val.length = selected.val.length ∧
      ∀ slot, slot < output.2.val.length →
        (slot < required.val.length ∧
          output.2.val[slot]? =
            (required.val[slot]?).map constructorCanonicalEdge) ∨
        ∃ node, node < componentCount.val ∧ node ≠ quotientRoot.val ∧
          slot = constructorSceneSelectedIndex required.val.length quotientRoot.val node ∧
          output.2.val[slot]? = some (chosen node)) := by
  have hcardinality :
      required.val.length + componentCount.val - 1 = selected.val.length := by
    omega
  exact constructor_scene_selected_actual_spec work required componentCount quotientRoot
    witnesses selected chosen hroot hincoming hwitness hcardinality

/-- The incoming-slot theorem supplies the concrete witness function used by the actual selection
loops, so no selected original edge is assumed. -/
theorem constructor_scene_selected_from_dfs_output_spec (work : spanning_tree.Workspace)
    (n : Usize) (required : Slice topology.Edge) (links : alloc.vec.Vec Usize)
    (componentCount quotientRoot : Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (selected : alloc.vec.Vec topology.Edge)
    (hroot : quotientRoot.val < componentCount.val)
    (hincomingCapacity : componentCount.val ≤ work.incoming.val.length)
    (hincoming : ∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
      ∃ retained : Usize × topology.Edge,
        work.incoming.val[node.val]? = some retained.1 ∧
        witnesses.val[retained.1.val]? = some retained.2)
    (hforestCount :
      required.val.length + constructorSceneRootCount links = n.val)
    (hcomponentCount :
      componentCount.val = constructorSceneRootCount links)
    (hselectedLength : selected.val.length = n.val - 1) :
    WP.spec (do
      let selected1 ← spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected
      spanning_tree.Tree.scene_dfs_loop7 work 0#usize componentCount witnesses
        quotientRoot selected1 (Slice.len required)) (fun output =>
      output.1 = work ∧ output.2.val.length = selected.val.length ∧
      ∀ slot, slot < output.2.val.length →
        (slot < required.val.length ∧
          output.2.val[slot]? =
            (required.val[slot]?).map constructorCanonicalEdge) ∨
        ∃ node, node < componentCount.val ∧ node ≠ quotientRoot.val ∧
          slot = constructorSceneSelectedIndex required.val.length quotientRoot.val node ∧
          output.2.val[slot]? =
            some (constructorSceneChosenWitness work witnesses node)) := by
  have hwitness : ∀ node : Usize, node.val < componentCount.val → node ≠ quotientRoot →
      ∃ slot : Usize, work.incoming.val[node.val]? = some slot ∧
        slot.val < witnesses.val.length ∧
        witnesses.val[slot.val]? =
          some (constructorSceneChosenWitness work witnesses node.val) := by
    intro node hnode hnonroot
    obtain ⟨⟨slot, edge⟩, hslot, hedge⟩ := hincoming node hnode hnonroot
    have hslotBound : slot.val < witnesses.val.length :=
      (List.getElem?_eq_some_iff.mp hedge).1
    refine ⟨slot, hslot, hslotBound, ?_⟩
    simpa only [constructor_scene_chosen_witness_eq work witnesses node.val slot edge hslot hedge]
      using hedge
  exact constructor_scene_selected_from_outputs_spec work n required links componentCount
    quotientRoot witnesses selected (constructorSceneChosenWitness work witnesses) hroot
    hincomingCapacity hwitness hforestCount hcomponentCount hselectedLength
end Labyrinth
