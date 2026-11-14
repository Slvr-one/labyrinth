module
public import LabyrinthCore.MutationTreeInterpretation
public import LabyrinthCore.MutationPath

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_follow_next (p : List Nat) (k v : Nat) :
    follow p (k + 1) v = parentAt p (follow p k v) := by
  have h := mutation_follow_add p 1 k v
  simpa only [Nat.add_comm 1 k, follow] using h

 theorem mutation_reroot_collect_exact
    (v : alloc.vec.Vec Usize) (root n start : Usize) (w : spanning_tree.Workspace)
    (k : Nat) (hn : n.val = v.val.length)
    (hp : ∀ x ∈ v.val.map (·.val), x < v.val.length)
    (hstart : start.val < n.val)
    (hreach : follow (v.val.map (·.val)) k start.val = root.val)
    (hfirst : ∀ j, j < k → follow (v.val.map (·.val)) j start.val ≠ root.val)
    (hk : k < n.val) (hw : WorkspaceValid w) (hcapacity : n.val ≤ w.path.val.length) :
    spanning_tree.Tree.reroot_loop0 v root w n start 0#usize ⦃ out =>
      WorkspaceValid out.1 ∧ out.1.path.val.length = w.path.val.length ∧
      out.2.1 = root ∧ out.2.2.val = k ∧
      ∀ j, j < k → ∃ node, out.1.path.val[j]? = some node ∧
        node.val = follow (v.val.map (·.val)) j start.val ⦄ := by
  let p := v.val.map (·.val)
  unfold spanning_tree.Tree.reroot_loop0
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize × Usize => k - state.2.2.val)
    (fun state : spanning_tree.Workspace × Usize × Usize =>
      WorkspaceValid state.1 ∧ state.1.path.val.length = w.path.val.length ∧
      state.2.2.val ≤ k ∧ state.2.1.val = follow p state.2.2.val start.val ∧
      ∀ j, j < state.2.2.val → ∃ node, state.1.path.val[j]? = some node ∧
        node.val = follow p j start.val)
    _
  · rintro ⟨scratch, current, used⟩ ⟨hvalid, hlen, hused, hcurrent, hnodes⟩
    dsimp only at hvalid hlen hused hcurrent hnodes ⊢
    have hcurrentBound : current.val < n.val := by
      rw [hcurrent]
      have hbound := mutation_follow_bound p (by simpa [p, hn] using hp)
        used.val start.val (by simpa [p, hn] using hstart)
      simpa [p, hn] using hbound
    have husedBound : used.val < n.val := by omega
    have hltCell : current < n := hcurrentBound
    have hltUsed : used < n := husedBound
    unfold spanning_tree.Tree.reroot_loop0.body
    simp only [hltCell, hltUsed, ite_true]
    by_cases heq : current = root
    · have husedEq : used.val = k := by
        by_contra hne
        have hsmall : used.val < k := by omega
        apply hfirst used.val hsmall
        exact hcurrent.symm.trans (congrArg UScalar.val heq)
      simpa [heq, hvalid, hlen, husedEq] using hnodes
    · have hbne : (current != root) = true := by simp [heq]
      simp only [hbne, ite_true]
      have husedLess : used.val < k := by
        by_contra hnot
        have he : used.val = k := by omega
        apply heq
        apply UScalar.eq_of_val_eq
        simpa [he, hreach, p] using hcurrent
      have hindex : used.val < scratch.path.val.length := by omega
      simp only [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.path used hindex)
      rintro ⟨old, back⟩ ⟨hold, hback⟩
      apply spec_bind (Usize.add_spec (x := used) (y := 1#usize) (by scalar_tac))
      intro used' hused'
      have hindexCurrent : current.val < v.val.length := by omega
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec v current hindexCurrent)
      intro next hnext
      have hnextval : next.val = parentAt p current.val := by
        rw [hnext]
        exact (mutation_parent_get v current hindexCurrent).symm
      have husedVal : used'.val = used.val + 1 := by simpa using hused'
      subst back
      simp only [spec_ok]
      refine ⟨⟨mutation_workspace_path_valid scratch _ hvalid (by simp),
        by simpa using hlen, by omega, ?_, ?_⟩, by omega⟩
      · rw [husedVal, mutation_follow_next, ← hcurrent]
        exact hnextval
      · intro j hj
        by_cases hjEq : j = used.val
        · exact ⟨current, by simp [hjEq, hindex], by simpa [hjEq] using hcurrent⟩
        · obtain ⟨node, hnode, hnodeval⟩ := hnodes j (by omega)
          exact ⟨node, by simpa [List.getElem?_set, hjEq, Ne.symm hjEq] using hnode, hnodeval⟩
  · exact ⟨hw, rfl, by simp, rfl, by simp⟩

 theorem mutation_reroot_reverse_exact
    (published path : alloc.vec.Vec Usize) (count : Usize)
    (hcount : 1 ≤ count.val) (hcapacity : count.val ≤ path.val.length)
    (hbounded : ∀ i, i < count.val → ∀ node,
      path.val[i]? = some node → node.val < published.val.length)
    (hunique : ∀ i j, i < count.val → j < count.val → ∀ x y,
      path.val[i]? = some x → path.val[j]? = some y → x.val = y.val → i = j) :
    spanning_tree.Tree.reroot_loop1 published path count 1#usize ⦃ result =>
      result.val.length = published.val.length ∧
      (∀ i, 1 ≤ i → i < count.val → ∀ node prev,
        path.val[i]? = some node → path.val[i - 1]? = some prev →
          result.val[node.val]? = some prev) ∧
      (∀ u, u < published.val.length →
        (∀ i, 1 ≤ i → i < count.val → ∀ node,
          path.val[i]? = some node → node.val ≠ u) →
        result.val[u]? = published.val[u]?) ⦄ := by
  let assigned := fun (current : alloc.vec.Vec Usize) (stop : Nat) =>
    ∀ i, 1 ≤ i → i < stop → ∀ node prev,
      path.val[i]? = some node → path.val[i - 1]? = some prev →
        current.val[node.val]? = some prev
  let unchanged := fun (current : alloc.vec.Vec Usize) (stop : Nat) =>
    ∀ u, u < published.val.length →
      (∀ i, 1 ≤ i → i < stop → ∀ node, path.val[i]? = some node → node.val ≠ u) →
      current.val[u]? = published.val[u]?
  unfold spanning_tree.Tree.reroot_loop1
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize => count.val - state.2.val)
    (fun state : alloc.vec.Vec Usize × Usize =>
      state.1.val.length = published.val.length ∧
      1 ≤ state.2.val ∧ state.2.val ≤ count.val ∧
      assigned state.1 state.2.val ∧ unchanged state.1 state.2.val)
    _
  · rintro ⟨current, j⟩ ⟨hlen, hj, hjc, hassigned, hunchanged⟩
    dsimp only at hlen hj hjc hassigned hunchanged ⊢
    unfold spanning_tree.Tree.reroot_loop1.body
    by_cases hlt : j < count
    · have hltNat : j.val < count.val := hlt
      simp only [hlt, ite_true]
      apply spec_bind (Usize.sub_spec (x := j) (y := 1#usize) (by simpa using hj))
      rintro previous ⟨hprevious, hsubBound⟩
      have hpreviousVal : previous.val = j.val - 1 := by simpa using hprevious
      have hpreviousBound : previous.val < path.val.length := by omega
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec path previous hpreviousBound)
      intro parent hparent
      have hjBound : j.val < path.val.length := by omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec path j hjBound)
      intro node hnode
      have hnodeGet : path.val[j.val]? = some node := by
        rw [List.getElem?_eq_getElem hjBound]
        exact congrArg some hnode.symm
      have hparentGet : path.val[j.val - 1]? = some parent := by
        rw [← hpreviousVal, List.getElem?_eq_getElem hpreviousBound]
        exact congrArg some hparent.symm
      have hnodeBound : node.val < current.val.length := by
        rw [hlen]
        exact hbounded j.val hltNat node hnodeGet
      simp only [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec current node hnodeBound)
      rintro ⟨old, back⟩ ⟨hold, hback⟩
      apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro next hnext
      have hnextVal : next.val = j.val + 1 := by simpa using hnext
      subst back
      simp only [spec_ok]
      refine ⟨⟨by simpa using hlen, by omega, by omega, ?_, ?_⟩, by omega⟩
      · intro i hi hin x prev hx hprev
        by_cases hij : i = j.val
        · have hxEq : x = node := by
            rw [hij, hnodeGet] at hx
            exact (Option.some.inj hx).symm
          have hpEq : prev = parent := by
            rw [hij, hparentGet] at hprev
            exact (Option.some.inj hprev).symm
          simp [hxEq, hpEq, hnodeBound]
        · have hiOld : i < j.val := by omega
          have hne : node.val ≠ x.val := by
            intro he
            exact hij (hunique i j.val (by omega) hltNat x node hx hnodeGet he.symm)
          have hwas := hassigned i hi hiOld x prev hx hprev
          simpa [List.getElem?_set, hne] using hwas
      · intro u hu hoff
        have hne : node.val ≠ u := hoff j.val hj (by omega) node hnodeGet
        have hold := hunchanged u hu (fun i hi hij x hx =>
          hoff i hi (by omega) x hx)
        simpa [List.getElem?_set, hne] using hold
    · have heq : j.val = count.val := by
        have hge : count.val ≤ j.val := Nat.le_of_not_lt hlt
        omega
      simpa [hlt, heq] using And.intro hlen (And.intro hassigned hunchanged)
  · refine ⟨rfl, by simp, by simpa using hcount, ?_, ?_⟩
    · intro i hi hil
      have : ¬ i < 1 := by omega
      exact (this hil).elim
    · intro u hu hoff
      rfl

end Labyrinth
