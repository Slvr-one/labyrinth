module
public import LabyrinthCore.MutationVirtualEdit

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 def MutationOverlayWithin (n : Nat) (w : spanning_tree.Workspace) : Prop :=
  ∀ u, n ≤ u → u < w.path.val.length → w.edit_slots.val[u]? = some core.num.Usize.MAX

 theorem mutation_overlay_active_bound (n : Nat) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hwithin : MutationOverlayWithin n w) :
    ∀ i, i < w.edit_count.val → ∀ node,
      w.edit_nodes.val[i]? = some node → node.val < n := by
  intro i hi node hnode
  obtain ⟨expected, hexpected, hbound, slot, hslot, hindex⟩ := hw.2.2.2.2.2.2.2.2.1 i hi
  have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
  by_contra hnot
  have hsentinel := hwithin expected.val (by simpa only [he] using Nat.le_of_not_lt hnot) hbound
  rw [hsentinel] at hslot
  have hs : core.num.Usize.MAX = slot := Option.some.inj hslot
  have hm : slot.val = Usize.max := by rw [← hs]; rfl
  have hcount := hw.2.2.2.2.2.2.1
  have hcap := w.path.property
  omega

 theorem mutation_clear_edits_within (n : Nat) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) :
    spanning_tree.Workspace.clear_edits w ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin n out ∧
      ∀ published u, mutationVirtualParent out published u =
        (published.val[u]?.getD 0#usize).val ⦄ := by
  apply spec_mono (mutation_clear_edits_total w hw)
  rintro out ⟨hvalid, hcount, hseen, hframes, hpath, hparents, hincoming, hnodes, hedge, hall⟩
  refine ⟨hvalid, hpath, ?_, ?_⟩
  · intro u _ hu
    exact hall u (by simpa only [hpath] using hu)
  · intro published u
    by_cases hu : u < w.path.val.length
    · simp [mutationVirtualParent, hall u hu]
    · have hslotslen := hvalid.2.2.2.2.1
      have hout : out.edit_slots.val[u]? = none := List.getElem?_eq_none (by
        rw [hslotslen, hpath]
        omega)
      simp [mutationVirtualParent, hout]

 theorem mutation_set_parent_within (n : Nat) (w : spanning_tree.Workspace)
    (cell parent : Usize) (hw : WorkspaceValid w)
    (hcell : cell.val < n) (hcapacity : n ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin n w) :
    spanning_tree.Workspace.set_parent w cell parent ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin n out ⦄ := by
  apply spec_mono (mutation_workspace_set_parent_total w cell parent hw (by omega))
  rintro out ⟨hvalid, hpath, _, _, _, _, _, hslots, _⟩
  refine ⟨hvalid, hpath, ?_⟩
  intro u hnu hu
  rw [hslots u (by omega)]
  exact hwithin u hnu (by simpa only [hpath] using hu)

 theorem mutation_virtual_reverse_within
    (n : Nat) (w : spanning_tree.Workspace) (count : Usize)
    (hw : WorkspaceValid w) (hwithin : MutationOverlayWithin n w)
    (hcapacity : n ≤ w.path.val.length) (hcount : 1 ≤ count.val)
    (hpathCapacity : count.val ≤ w.path.val.length)
    (hpathNodes : ∀ i, i < count.val → ∀ node, w.path.val[i]? = some node → node.val < n) :
    spanning_tree.Tree.attach_virtual_loop1 w count 1#usize ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin n out ⦄ := by
  unfold spanning_tree.Tree.attach_virtual_loop1
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize => count.val - state.2.val)
    (fun state : spanning_tree.Workspace × Usize =>
      WorkspaceValid state.1 ∧ state.1.path = w.path ∧ MutationOverlayWithin n state.1 ∧
      1 ≤ state.2.val ∧ state.2.val ≤ count.val)
    _
  · rintro ⟨scratch, j⟩ ⟨hvalid, hpath, hinside, hj, hjc⟩
    dsimp only at hvalid hpath hinside hj hjc ⊢
    unfold spanning_tree.Tree.attach_virtual_loop1.body
    by_cases hlt : j < count
    · have hjlt : j.val < count.val := hlt
      simp only [hlt, ite_true, alloc.vec.Vec.index_slice_index]
      have hjBound : j.val < scratch.path.val.length := by rw [hpath]; omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec scratch.path j hjBound)
      intro node hnode
      apply spec_bind (Usize.sub_spec (x := j) (y := 1#usize) (by simpa using hj))
      rintro previous ⟨hprevious, _⟩
      have hpreviousVal : previous.val = j.val - 1 := by simpa using hprevious
      apply spec_bind (alloc.vec.Vec.index_usize_spec scratch.path previous (by rw [hpath]; omega))
      intro parent hparent
      have hnodeGet : w.path.val[j.val]? = some node := by
        rw [← hpath, List.getElem?_eq_getElem hjBound]
        exact congrArg some hnode.symm
      apply spec_bind (mutation_set_parent_within n scratch node parent hvalid
        (hpathNodes j.val hjlt node hnodeGet) (by simpa only [hpath] using hcapacity) hinside)
      rintro nextWork ⟨hnextValid, hnextPath, hnextWithin⟩
      apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro next hnext
      have hnextVal : next.val = j.val + 1 := by simpa using hnext
      simp only [spec_ok]
      exact ⟨⟨hnextValid, hnextPath.trans hpath, hnextWithin, by omega, by omega⟩, by omega⟩
    · simpa [hlt] using And.intro hvalid (And.intro hpath hinside)
  · exact ⟨hw, rfl, hwithin, by simp, by simpa using hcount⟩

end Labyrinth
