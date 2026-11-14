module
public import LabyrinthCore.Mutations
public import LabyrinthCore.MutationOverlay

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_workspace_nodes_nodup (w : spanning_tree.Workspace)
    (hforward : ∀ i, i < w.edit_count.val →
      ∃ node, w.edit_nodes.val[i]? = some node ∧ node.val < w.path.val.length ∧
        ∃ slot, w.edit_slots.val[node.val]? = some slot ∧ slot.val = i) :
    ((w.edit_nodes.val.take w.edit_count.val).map (·.val)).Nodup := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro i j hij hj heq
  have hjcount : j < w.edit_count.val := by
    simp only [List.length_map, List.length_take] at hj
    omega
  obtain ⟨a, ha, _, sa, hsa, hia⟩ := hforward i (by omega)
  obtain ⟨b, hb, _, sb, hsb, hjb⟩ := hforward j hjcount
  have hab : a.val = b.val := by
    simpa [List.getElem?_map, List.getElem?_take, ha, hb,
      show i < w.edit_count.val by omega, hjcount] using heq
  rw [hab, hsb] at hsa
  have hs : sb = sa := Option.some.inj hsa
  have : i = j := hia.symm.trans ((congrArg UScalar.val hs.symm).trans hjb)
  omega

 theorem mutation_workspace_existing_parent_valid
    (w : spanning_tree.Workspace) (slot parent : Usize)
    (hw : WorkspaceValid w) :
    WorkspaceValid { w with parents := w.parents.set slot parent } := by
  simpa only [WorkspaceValid, alloc.vec.Vec.set_val_eq, List.length_set] using hw

 theorem mutation_workspace_new_parent_valid
    (w : spanning_tree.Workspace) (cell parent count : Usize)
    (hw : WorkspaceValid w) (hc : cell.val < w.path.val.length)
    (hempty : w.edit_slots.val[cell.val]? = some core.num.Usize.MAX)
    (hcount : count.val = w.edit_count.val + 1) :
    WorkspaceValid { w with
      parents := w.parents.set w.edit_count parent,
      edit_slots := w.edit_slots.set cell w.edit_count,
      edit_nodes := w.edit_nodes.set w.edit_count cell,
      edit_count := count } := by
  have hroom := mutation_empty_slot_has_capacity w hw cell hc hempty
  rcases hw with ⟨hseen, hframes, hparents, hincoming, hslots, hnodes,
    hused, hnodup, hforward, hlookup⟩
  let out : spanning_tree.Workspace := { w with
    parents := w.parents.set w.edit_count parent,
    edit_slots := w.edit_slots.set cell w.edit_count,
    edit_nodes := w.edit_nodes.set w.edit_count cell,
    edit_count := count }
  have hforward' : ∀ i, i < out.edit_count.val →
      ∃ node, out.edit_nodes.val[i]? = some node ∧ node.val < out.path.val.length ∧
        ∃ slot, out.edit_slots.val[node.val]? = some slot ∧ slot.val = i := by
    intro i hi
    by_cases heq : i = w.edit_count.val
    · refine ⟨cell, ?_, hc, w.edit_count, ?_, heq.symm⟩
      · simp [out, heq, show w.edit_count.val < w.edit_nodes.val.length by omega]
      · simp [out, show cell.val < w.edit_slots.val.length by omega]
    · have hiold : i < w.edit_count.val := by
        dsimp only [out] at hi
        omega
      obtain ⟨node, hnode, hbound, slot, hslot, hindex⟩ := hforward i hiold
      have hne : node.val ≠ cell.val := by
        intro he
        rw [he, hempty] at hslot
        have hs : core.num.Usize.MAX = slot := Option.some.inj hslot
        have hm : slot.val = Usize.max := by rw [← hs]; rfl
        have hmax := w.path.property
        omega
      refine ⟨node, ?_, hbound, slot, ?_, hindex⟩
      · simpa [out, List.getElem?_set, heq, Ne.symm heq] using hnode
      · simpa [out, List.getElem?_set, hne, Ne.symm hne] using hslot
  have hlookup' : ∀ node, node < out.path.val.length →
      ∃ slot, out.edit_slots.val[node]? = some slot ∧
        (slot.val = Usize.max ∨
          (slot.val < out.edit_count.val ∧
            ∃ value, out.edit_nodes.val[slot.val]? = some value ∧ value.val = node)) := by
    intro node hn
    by_cases heq : node = cell.val
    · refine ⟨w.edit_count, ?_, Or.inr ⟨by dsimp [out]; omega, cell, ?_, heq.symm⟩⟩
      · simp [out, heq, show cell.val < w.edit_slots.val.length by omega]
      · simp [out, show w.edit_count.val < w.edit_nodes.val.length by omega]
    · obtain ⟨slot, hslot, hmax | hactive⟩ := hlookup node hn
      · exact ⟨slot, by simpa [out, List.getElem?_set, heq, Ne.symm heq] using hslot,
          Or.inl hmax⟩
      · obtain ⟨hlt, value, hvalue, hvalueEq⟩ := hactive
        refine ⟨slot, ?_, Or.inr ⟨by dsimp [out]; omega, value, ?_, hvalueEq⟩⟩
        · simpa [out, List.getElem?_set, heq, Ne.symm heq] using hslot
        · simpa [out, List.getElem?_set, Nat.ne_of_lt hlt, Ne.symm (Nat.ne_of_lt hlt)] using hvalue
  change WorkspaceValid out
  refine ⟨hseen, hframes, ?_, hincoming, ?_, ?_, ?_,
    mutation_workspace_nodes_nodup out hforward', hforward', hlookup'⟩
  · simpa [out] using hparents
  · simpa [out] using hslots
  · simpa [out] using hnodes
  · dsimp [out]
    omega

 theorem mutation_workspace_set_parent_total
    (w : spanning_tree.Workspace) (cell parent : Usize)
    (hw : WorkspaceValid w) (hc : cell.val < w.path.val.length) :
    spanning_tree.Workspace.set_parent w cell parent ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ out.seen = w.seen ∧
      out.frames = w.frames ∧ out.incoming = w.incoming ∧
      out.edge_capacity = w.edge_capacity ∧
      (∃ slot, out.edit_slots.val[cell.val]? = some slot ∧
        slot.val < out.edit_count.val ∧ out.parents.val[slot.val]? = some parent) ∧
      (∀ node, node ≠ cell.val → out.edit_slots.val[node]? = w.edit_slots.val[node]?) ∧
      (∀ slot : Usize, slot.val < w.edit_count.val →
        w.edit_slots.val[cell.val]? ≠ some slot →
        out.parents.val[slot.val]? = w.parents.val[slot.val]?) ⦄ := by
  have hslen := hw.2.2.2.2.1
  have hplen := hw.2.2.1
  have hnlen := hw.2.2.2.2.2.1
  have hused := hw.2.2.2.2.2.2.1
  obtain ⟨slot, hslot, hcases⟩ := hw.2.2.2.2.2.2.2.2.2 cell.val hc
  have hsbound : cell.val < w.edit_slots.val.length := by omega
  unfold spanning_tree.Workspace.set_parent
  simp only [alloc.vec.Vec.index_slice_index]
  apply spec_bind (alloc.vec.Vec.index_usize_spec w.edit_slots cell hsbound)
  intro actual hactual
  have heq : actual = slot := by
    rw [List.getElem?_eq_getElem hsbound] at hslot
    exact hactual.trans (Option.some.inj hslot)
  rw [heq]
  by_cases hempty : slot = core.num.Usize.MAX
  · have hemptyGet : w.edit_slots.val[cell.val]? = some core.num.Usize.MAX := by
      simpa [hempty] using hslot
    have hroom := mutation_empty_slot_has_capacity w hw cell hc hemptyGet
    simp only [hempty, ite_true, Std.bind_assoc]
    apply spec_bind (Usize.add_spec (x := w.edit_count) (y := 1#usize) (by
      have := w.path.property
      scalar_tac))
    intro count hcount
    simp only [alloc.vec.Vec.index_mut_slice_index]
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec w.edit_slots cell hsbound)
    rintro ⟨oldSlot, backSlot⟩ ⟨_, hbackSlot⟩
    change (do
      let (slots, nodes, used, index) ← (do
        let (_, backNode) ← w.edit_nodes.index_mut_usize w.edit_count
        Result.ok (backSlot w.edit_count, backNode cell, count, w.edit_count))
      let (_, backParent) ← w.parents.index_mut_usize index
      Result.ok { w with
        parents := backParent parent, edit_slots := slots,
        edit_nodes := nodes, edit_count := used }) ⦃ _ ⦄
    simp only [Std.bind_assoc]
    have hnodeBound : w.edit_count.val < w.edit_nodes.val.length := by omega
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec w.edit_nodes w.edit_count hnodeBound)
    rintro ⟨oldNode, backNode⟩ ⟨_, hbackNode⟩
    change (do
      let (_, backParent) ← w.parents.index_mut_usize w.edit_count
      Result.ok { w with
        parents := backParent parent
        edit_slots := backSlot w.edit_count
        edit_nodes := backNode cell
        edit_count := count }) ⦃ _ ⦄
    have hparentBound : w.edit_count.val < w.parents.val.length := by omega
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec w.parents w.edit_count hparentBound)
    rintro ⟨oldParent, backParent⟩ ⟨_, hbackParent⟩
    subst backSlot
    subst backNode
    subst backParent
    apply (spec_ok _).mpr
    refine ⟨mutation_workspace_new_parent_valid w cell parent count hw hc hemptyGet
      (by simpa using hcount), rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · refine ⟨w.edit_count, by simp [hsbound], ?_,
        by simp [show w.edit_count.val < w.parents.val.length by omega]⟩
      have hcountval : count.val = w.edit_count.val + 1 := by simpa using hcount
      omega
    · intro node hne
      simp [List.getElem?_set, hne, Ne.symm hne]
    · intro index hindex _
      simp [List.getElem?_set, Nat.ne_of_lt hindex, Ne.symm (Nat.ne_of_lt hindex)]
  · simp only [hempty, ite_false, bind_ok, alloc.vec.Vec.index_mut_slice_index]
    have hnotmax : slot.val ≠ Usize.max := by
      intro he
      apply hempty
      apply UScalar.eq_of_val_eq
      exact he
    have hactive : slot.val < w.edit_count.val := (hcases.resolve_left hnotmax).1
    have hpbound : slot.val < w.parents.val.length := by omega
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec w.parents slot hpbound)
    rintro ⟨oldParent, backParent⟩ ⟨_, hbackParent⟩
    subst backParent
    apply (spec_ok _).mpr
    refine ⟨mutation_workspace_existing_parent_valid w slot parent hw,
      rfl, rfl, rfl, rfl, rfl, ⟨slot, hslot, hactive, by simp [hpbound]⟩,
      fun _ _ => rfl, ?_⟩
    intro index hindex hne
    have hdiff : index.val ≠ slot.val := by
      intro he
      apply hne
      have hscalar : index = slot := UScalar.eq_of_val_eq he
      simpa [hscalar] using hslot
    simp [Ne.symm hdiff]

end Labyrinth
