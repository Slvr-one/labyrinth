module
public import LabyrinthCore.MutationVirtualEdit

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_commit_total
    (v : alloc.vec.Vec Usize) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : v.val.length ≤ w.path.val.length)
    (hactive : ∀ i, i < w.edit_count.val → ∀ node,
      w.edit_nodes.val[i]? = some node → node.val < v.val.length) :
    spanning_tree.Tree.edit_edges_loop3 v w 0#usize ⦃ out =>
      ∃ result : alloc.vec.Vec Usize,
        out = (result, w.seen, w.frames, w.path, w.parents, w.incoming,
          w.edit_slots, w.edit_nodes, w.edit_count, w.edge_capacity) ∧
        result.val.length = v.val.length ∧
        ∀ u, u < v.val.length →
          (result.val[u]?.getD 0#usize).val =
            mutationVirtualParent w (alloc.vec.Vec.deref v) u ⦄ := by
  let assigned := fun (current : alloc.vec.Vec Usize) (stop : Nat) =>
    ∀ i, i < stop → ∀ node value,
      w.edit_nodes.val[i]? = some node → w.parents.val[i]? = some value →
        current.val[node.val]? = some value
  let unchanged := fun (current : alloc.vec.Vec Usize) (stop : Nat) =>
    ∀ u, u < v.val.length →
      (∀ i, i < stop → ∀ node, w.edit_nodes.val[i]? = some node → node.val ≠ u) →
      current.val[u]? = v.val[u]?
  have hcount := hw.2.2.2.2.2.2.1
  have hparents := hw.2.2.1
  have hnodes := hw.2.2.2.2.2.1
  have hforward := hw.2.2.2.2.2.2.2.2.1
  have hlookup := hw.2.2.2.2.2.2.2.2.2
  unfold spanning_tree.Tree.edit_edges_loop3
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize => w.edit_count.val - state.2.val)
    (fun state : alloc.vec.Vec Usize × Usize =>
      state.1.val.length = v.val.length ∧ state.2.val ≤ w.edit_count.val ∧
      assigned state.1 state.2.val ∧ unchanged state.1 state.2.val)
    _
  · rintro ⟨current, i⟩ ⟨hlen, hi, hassigned, hunchanged⟩
    dsimp only at hlen hi hassigned hunchanged ⊢
    unfold spanning_tree.Tree.edit_edges_loop3.body
    by_cases hlt : i < w.edit_count
    · have hltNat : i.val < w.edit_count.val := hlt
      simp only [hlt, ite_true, alloc.vec.Vec.index_slice_index]
      have hip : i.val < w.parents.val.length := by omega
      have hin : i.val < w.edit_nodes.val.length := by omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec w.parents i hip)
      intro value hvalue
      apply spec_bind (alloc.vec.Vec.index_usize_spec w.edit_nodes i hin)
      intro node hnode
      have hvalueGet : w.parents.val[i.val]? = some value := by
        rw [List.getElem?_eq_getElem hip]
        exact congrArg some hvalue.symm
      have hnodeGet : w.edit_nodes.val[i.val]? = some node := by
        rw [List.getElem?_eq_getElem hin]
        exact congrArg some hnode.symm
      have hnodeBound : node.val < current.val.length := by
        rw [hlen]
        exact hactive i.val hltNat node hnodeGet
      simp only [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec current node hnodeBound)
      rintro ⟨old, back⟩ ⟨_, hback⟩
      apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro next hnext
      have hnextVal : next.val = i.val + 1 := by simpa using hnext
      subst back
      simp only [spec_ok]
      refine ⟨⟨by simpa using hlen, by omega, ?_, ?_⟩, by omega⟩
      · intro j hj other otherValue hother hotherValue
        by_cases heq : j = i.val
        · have hn : other = node := by
            rw [heq, hnodeGet] at hother
            exact (Option.some.inj hother).symm
          have hv : otherValue = value := by
            rw [heq, hvalueGet] at hotherValue
            exact (Option.some.inj hotherValue).symm
          simp [hn, hv, hnodeBound]
        · have hjold : j < i.val := by omega
          have hne : node.val ≠ other.val := by
            intro he
            obtain ⟨a, ha, _, sa, hsa, hsia⟩ := hforward i.val hltNat
            obtain ⟨b, hb, _, sb, hsb, hsib⟩ := hforward j (by omega)
            have hna : node = a := Option.some.inj (hnodeGet.symm.trans ha)
            have hnb : other = b := Option.some.inj (hother.symm.trans hb)
            have hab : a.val = b.val := by simpa only [hna, hnb] using he
            rw [hab, hsb] at hsa
            have hs : sb = sa := Option.some.inj hsa
            have hij : i.val = j := hsia.symm.trans ((congrArg UScalar.val hs.symm).trans hsib)
            omega
          simpa [List.getElem?_set, hne] using hassigned j hjold other otherValue hother hotherValue
      · intro u hu hoff
        have hne : node.val ≠ u := hoff i.val (by omega) node hnodeGet
        simpa [List.getElem?_set, hne] using
          hunchanged u hu (fun j hj x hx => hoff j (by omega) x hx)
    · have heq : i.val = w.edit_count.val := by
        have hge : w.edit_count.val ≤ i.val := Nat.le_of_not_lt hlt
        omega
      simp only [hlt, ite_false, spec_ok]
      refine ⟨current, rfl, hlen, ?_⟩
      intro u hu
      obtain ⟨slot, hslot, hmax | hslotActive⟩ := hlookup u (by omega)
      · have hs : slot = core.num.Usize.MAX := UScalar.eq_of_val_eq hmax
        have hoff : ∀ j, j < i.val → ∀ node,
            w.edit_nodes.val[j]? = some node → node.val ≠ u := by
          intro j hj node hnode hnodeEq
          obtain ⟨expected, hexpected, _, actualSlot, hactualSlot, hindex⟩ :=
            hforward j (by omega)
          have hn : node = expected := Option.some.inj (hnode.symm.trans hexpected)
          rw [← hn, hnodeEq, hslot] at hactualSlot
          have he : slot = actualSlot := Option.some.inj hactualSlot
          have hm : actualSlot.val = Usize.max := by rw [← he]; exact hmax
          have hcap := w.path.property
          omega
        have hsame := hunchanged u hu hoff
        simp [mutationVirtualParent, hslot, hs, hsame]
      · obtain ⟨hslotLt, node, hnode, hnodeVal⟩ := hslotActive
        have hip : slot.val < w.parents.val.length := by omega
        let value := w.parents.val[slot.val]
        have hvalue : w.parents.val[slot.val]? = some value := by
          simp [value, hip]
        have hset := hassigned slot.val (by omega) node value hnode hvalue
        have hnotmax : slot ≠ core.num.Usize.MAX := by
          intro hs
          have hm : slot.val = Usize.max := by rw [hs]; rfl
          have hcap := w.path.property
          omega
        rw [hnodeVal] at hset
        simp [mutationVirtualParent, hslot, hnotmax, hvalue, hset]
  · exact ⟨rfl, by simp, by simp [assigned], by simp [unchanged]⟩

end Labyrinth
