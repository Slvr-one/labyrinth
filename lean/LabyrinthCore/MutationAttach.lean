module
public import LabyrinthCore.MutationVirtualEdit
public import LabyrinthCore.MutationRerootSpec

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_virtual_reverse_exact
    (w : spanning_tree.Workspace) (published : Slice Usize) (count : Usize)
    (hw : WorkspaceValid w) (hcount : 1 ≤ count.val)
    (hcapacity : count.val ≤ w.path.val.length)
    (hbounded : ∀ i, i < count.val → ∀ node,
      w.path.val[i]? = some node → node.val < w.path.val.length)
    (hunique : ∀ i j, i < count.val → j < count.val → ∀ x y,
      w.path.val[i]? = some x → w.path.val[j]? = some y → x.val = y.val → i = j) :
    spanning_tree.Tree.attach_virtual_loop1 w count 1#usize ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧
      (∀ i, 1 ≤ i → i < count.val → ∀ node prev,
        w.path.val[i]? = some node → w.path.val[i - 1]? = some prev →
          mutationVirtualParent out published node.val = prev.val) ∧
      (∀ u, u < w.path.val.length →
        (∀ i, 1 ≤ i → i < count.val → ∀ node,
          w.path.val[i]? = some node → node.val ≠ u) →
        mutationVirtualParent out published u = mutationVirtualParent w published u) ⦄ := by
  let assigned := fun (current : spanning_tree.Workspace) (stop : Nat) =>
    ∀ i, 1 ≤ i → i < stop → ∀ node prev,
      w.path.val[i]? = some node → w.path.val[i - 1]? = some prev →
        mutationVirtualParent current published node.val = prev.val
  let unchanged := fun (current : spanning_tree.Workspace) (stop : Nat) =>
    ∀ u, u < w.path.val.length →
      (∀ i, 1 ≤ i → i < stop → ∀ node,
        w.path.val[i]? = some node → node.val ≠ u) →
      mutationVirtualParent current published u = mutationVirtualParent w published u
  unfold spanning_tree.Tree.attach_virtual_loop1
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize => count.val - state.2.val)
    (fun state : spanning_tree.Workspace × Usize =>
      WorkspaceValid state.1 ∧ state.1.path = w.path ∧
      1 ≤ state.2.val ∧ state.2.val ≤ count.val ∧
      assigned state.1 state.2.val ∧ unchanged state.1 state.2.val)
    _
  · rintro ⟨scratch, j⟩ ⟨hvalid, hpath, hj, hjc, hassigned, hunchanged⟩
    dsimp only at hvalid hpath hj hjc hassigned hunchanged ⊢
    unfold spanning_tree.Tree.attach_virtual_loop1.body
    by_cases hlt : j < count
    · have hltNat : j.val < count.val := hlt
      simp only [hlt, ite_true, alloc.vec.Vec.index_slice_index]
      have hjBound : j.val < scratch.path.val.length := by rw [hpath]; omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec scratch.path j hjBound)
      intro node hnode
      apply spec_bind (Usize.sub_spec (x := j) (y := 1#usize) (by simpa using hj))
      rintro previous ⟨hprevious, _⟩
      have hpreviousVal : previous.val = j.val - 1 := by simpa using hprevious
      have hpreviousBound : previous.val < scratch.path.val.length := by rw [hpath]; omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec scratch.path previous hpreviousBound)
      intro parent hparent
      have hnodeGet : w.path.val[j.val]? = some node := by
        rw [← hpath, List.getElem?_eq_getElem hjBound]
        exact congrArg some hnode.symm
      have hparentGet : w.path.val[j.val - 1]? = some parent := by
        rw [← hpath, ← hpreviousVal, List.getElem?_eq_getElem hpreviousBound]
        exact congrArg some hparent.symm
      have hnodeBound : node.val < scratch.path.val.length := by
        rw [hpath]
        exact hbounded j.val hltNat node hnodeGet
      apply spec_bind (mutation_workspace_set_parent_exact scratch node parent published hvalid hnodeBound)
      rintro nextWork ⟨hnextValid, hnextPath, _, _, _, _, hupdate⟩
      apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro next hnext
      have hnextVal : next.val = j.val + 1 := by simpa using hnext
      simp only [spec_ok]
      refine ⟨⟨hnextValid, hnextPath.trans hpath, by omega, by omega, ?_, ?_⟩, by omega⟩
      · intro i hi hin x prev hx hprev
        by_cases hij : i = j.val
        · have hxEq : x = node := by
            rw [hij, hnodeGet] at hx
            exact (Option.some.inj hx).symm
          have hpEq : prev = parent := by
            rw [hij, hparentGet] at hprev
            exact (Option.some.inj hprev).symm
          simpa [hxEq, hpEq] using hupdate node.val hnodeBound
        · have hiOld : i < j.val := by omega
          have hne : x.val ≠ node.val := by
            intro he
            exact hij (hunique i j.val (by omega) hltNat x node hx hnodeGet he)
          have hxBound : x.val < scratch.path.val.length := by
            rw [hpath]
            exact hbounded i (by omega) x hx
          rw [hupdate x.val hxBound, if_neg hne]
          exact hassigned i hi hiOld x prev hx hprev
      · intro u hu hoff
        have hne : u ≠ node.val := Ne.symm (hoff j.val hj (by omega) node hnodeGet)
        rw [hupdate u (by simpa only [hpath] using hu), if_neg hne]
        exact hunchanged u hu (fun i hi hij x hx => hoff i hi (by omega) x hx)
    · have heq : j.val = count.val := by
        have hge : count.val ≤ j.val := Nat.le_of_not_lt hlt
        omega
      simpa [hlt, heq] using And.intro hvalid (And.intro hpath (And.intro hassigned hunchanged))
  · refine ⟨hw, rfl, by simp, by simpa using hcount, ?_, ?_⟩
    · intro i hi hil
      omega
    · intro u hu hoff
      rfl

 theorem mutation_virtual_collect_exact
    (v : alloc.vec.Vec Usize) (w : spanning_tree.Workspace)
    (n root start : Usize) (k : Nat)
    (hn : n.val = v.val.length) (hw : WorkspaceValid w)
    (hcapacity : n.val ≤ w.path.val.length)
    (hbound : ∀ j, j ≤ k →
      (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] start.val < n.val)
    (hreach : (mutationVirtualParent w (alloc.vec.Vec.deref v))^[k] start.val = root.val)
    (hfirst : ∀ j, j < k →
      (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] start.val ≠ root.val)
    (hk : k < n.val) :
    spanning_tree.Tree.attach_virtual_loop0 v w n root start 0#usize ⦃ out =>
      WorkspaceValid out.1 ∧ out.1.path.val.length = w.path.val.length ∧
      out.1.parents = w.parents ∧ out.1.edit_slots = w.edit_slots ∧
      out.2.1 = root ∧ out.2.2.val = k ∧
      ∀ j, j < k → ∃ node, out.1.path.val[j]? = some node ∧
        node.val = (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] start.val ⦄ := by
  let next := mutationVirtualParent w (alloc.vec.Vec.deref v)
  unfold spanning_tree.Tree.attach_virtual_loop0
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize × Usize => k - state.2.2.val)
    (fun state : spanning_tree.Workspace × Usize × Usize =>
      WorkspaceValid state.1 ∧ state.1.path.val.length = w.path.val.length ∧
      state.1.parents = w.parents ∧ state.1.edit_slots = w.edit_slots ∧
      state.2.2.val ≤ k ∧ state.2.1.val = next^[state.2.2.val] start.val ∧
      ∀ j, j < state.2.2.val → ∃ node, state.1.path.val[j]? = some node ∧
        node.val = next^[j] start.val)
    _
  · rintro ⟨scratch, current, used⟩
      ⟨hvalid, hlen, hparents, hslots, hused, hcurrent, hnodes⟩
    dsimp only at hvalid hlen hparents hslots hused hcurrent hnodes ⊢
    have hcurrentBound : current.val < n.val := by
      rw [hcurrent]
      exact hbound used.val hused
    have husedBound : used.val < n.val := by omega
    have hltCell : current < n := hcurrentBound
    have hltUsed : used < n := husedBound
    unfold spanning_tree.Tree.attach_virtual_loop0.body
    simp only [hltCell, hltUsed, ite_true]
    by_cases heq : current = root
    · have husedEq : used.val = k := by
        by_contra hne
        apply hfirst used.val (by omega)
        exact hcurrent.symm.trans (congrArg UScalar.val heq)
      simpa [heq, hvalid, hlen, hparents, hslots, husedEq] using hnodes
    · have hbne : (current != root) = true := by simp [heq]
      simp only [hbne, ite_true, alloc.vec.Vec.index_mut_slice_index]
      have husedLess : used.val < k := by
        by_contra hnot
        have he : used.val = k := by omega
        apply heq
        apply UScalar.eq_of_val_eq
        simpa only [he, hreach] using hcurrent
      have hindex : used.val < scratch.path.val.length := by omega
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.path used hindex)
      rintro ⟨old, back⟩ ⟨_, hback⟩
      apply spec_bind (Usize.add_spec (x := used) (y := 1#usize) (by scalar_tac))
      intro used' hused'
      have husedVal : used'.val = used.val + 1 := by simpa using hused'
      subst back
      have hnewValid := mutation_workspace_path_valid scratch
        (scratch.path.set used current) hvalid (by simp)
      apply spec_bind (mutation_workspace_parent_exact
        { scratch with path := scratch.path.set used current } (alloc.vec.Vec.deref v)
        current hnewValid (by simp; omega) (by simpa only [hn] using hcurrentBound))
      intro parent hparent
      have hparentVal : parent.val = next current.val := by
        simpa only [mutationVirtualParent, next, hparents, hslots] using hparent
      simp only [spec_ok]
      refine ⟨⟨hnewValid, by simpa using hlen, hparents, hslots, by omega, ?_, ?_⟩,
        by omega⟩
      · rw [husedVal, Function.iterate_succ_apply', ← hcurrent]
        exact hparentVal
      · intro j hj
        by_cases hjEq : j = used.val
        · exact ⟨current, by simp [hjEq, hindex], by simpa [hjEq] using hcurrent⟩
        · obtain ⟨node, hnode, hnodeval⟩ := hnodes j (by omega)
          exact ⟨node, by simpa [List.getElem?_set, hjEq, Ne.symm hjEq] using hnode,
            hnodeval⟩
  · exact ⟨hw, rfl, rfl, rfl, by simp, rfl, by simp⟩

end Labyrinth
