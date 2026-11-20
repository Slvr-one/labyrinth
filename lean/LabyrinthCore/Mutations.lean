module
public import LabyrinthCore.Model

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_follow_fixed (p : List Nat) (root : Nat)
    (hroot : parentAt p root = root) (k : Nat) : follow p k root = root := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [follow, hroot] using ih

 theorem mutation_follow_add (p : List Nat) (a b v : Nat) :
    follow p (a + b) v = follow p a (follow p b v) := by
  induction b generalizing v with
  | zero => simp [follow]
  | succ b ih => simpa [Nat.add_succ, follow] using ih (parentAt p v)

 theorem mutation_parentAt_bound (p : List Nat)
    (hp : ∀ x ∈ p, x < p.length) (v : Nat) (hv : v < p.length) :
    parentAt p v < p.length := by
  simp only [parentAt, List.getElem?_eq_getElem hv, Option.getD_some]
  exact hp _ (List.getElem_mem hv)

 theorem mutation_follow_bound (p : List Nat)
    (hp : ∀ x ∈ p, x < p.length) (k v : Nat) (hv : v < p.length) :
    follow p k v < p.length := by
  induction k generalizing v with
  | zero => exact hv
  | succ k ih => exact ih _ (mutation_parentAt_bound p hp v hv)

 theorem mutation_rooted_fixed (p : List Nat) (root : Nat)
    (h : RootedTree p root) : parentAt p root = root := by
  simp [parentAt, h.2.1]

 theorem mutation_parent_get (v : alloc.vec.Vec Usize) (cell : Usize)
    (hc : cell.val < v.val.length) :
    parentAt (v.val.map (·.val)) cell.val = v.val[cell.val].val := by
  simp [parentAt, hc]

 theorem mutation_validate_walk_total
    (v : alloc.vec.Vec Usize) (root n cell steps : Usize)
    (hn : n.val = v.val.length)
    (hp : ∀ x ∈ v.val.map (·.val), x < v.val.length)
    (hr : parentAt (v.val.map (·.val)) root.val = root.val)
    (hc : cell.val < n.val) (hs : steps.val ≤ n.val) :
    spanning_tree.Tree.validate_loop0_loop0 v root n cell steps ⦃ result =>
      result.val = follow (v.val.map (·.val)) (n.val - steps.val) cell.val ⦄ := by
  let p := v.val.map (·.val)
  let answer := follow p (n.val - steps.val) cell.val
  unfold spanning_tree.Tree.validate_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : Usize × Usize => n.val - state.2.val)
    (fun state : Usize × Usize =>
      state.1.val < n.val ∧ state.2.val ≤ n.val ∧
      follow p (n.val - state.2.val) state.1.val = answer)
    (fun result : Usize => result.val = answer)
  · rintro ⟨current, count⟩ ⟨hcurrent, hcount, hanswer⟩
    dsimp only at hcurrent hcount hanswer ⊢
    unfold spanning_tree.Tree.validate_loop0_loop0.body
    by_cases heq : current = root
    · subst current
      simpa [mutation_follow_fixed p root.val hr, answer] using
        hanswer
    · have hbne : (current != root) = true := by simp [heq]
      have hlt : current < n := by exact hcurrent
      simp only [hbne, hlt, ite_true]
      by_cases hstep : count < n
      · simp only [hstep, ite_true, alloc.vec.Vec.index_slice_index]
        have hi : current.val < v.val.length := by omega
        apply spec_bind (alloc.vec.Vec.index_usize_spec v current hi)
        intro next hnext
        apply spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
          have := n.hmax
          scalar_tac))
        intro count' hcount'
        simp only [spec_ok]
        have hnextval : next.val = parentAt p current.val := by
          rw [hnext]
          exact (mutation_parent_get v current hi).symm
        have hnextbound : next.val < n.val := by
          rw [hnextval]
          have h := mutation_parentAt_bound p (by simpa [p, hn] using hp)
            current.val (by simpa [p, hn] using hcurrent)
          simpa [p, hn] using h
        have hstepval : count.val < n.val := hstep
        have hcountval : count'.val = count.val + 1 := by simpa using hcount'
        refine ⟨⟨hnextbound, by omega, ?_⟩, by omega⟩
        have hremaining : n.val - count.val = (n.val - count'.val) + 1 := by omega
        rw [hremaining, follow] at hanswer
        simpa [hnextval] using hanswer
      · simp only [hstep, ite_false, spec_ok]
        have hcountval : count.val = n.val := by
          have : ¬ count.val < n.val := hstep
          omega
        simpa [hcountval, follow] using hanswer
  · exact ⟨hc, hs, rfl⟩

 theorem mutation_workspace_parent_total
    (w : spanning_tree.Workspace) (published : Slice Usize) (cell : Usize)
    (hw : WorkspaceValid w)
    (hc : cell.val < w.path.val.length)
    (hpublished : cell.val < published.val.length) :
    spanning_tree.Workspace.parent w published cell ⦃ value =>
      (∃ slot, w.edit_slots.val[cell.val]? = some slot ∧
        ((slot.val = Usize.max ∧ published.val[cell.val]? = some value) ∨
         (slot.val < w.edit_count.val ∧ w.parents.val[slot.val]? = some value))) ⦄ := by
  rcases hw with ⟨_, _, hparents, _, hslots, _, hcount, _, _, hlookup⟩
  obtain ⟨slot, hslot, hcases⟩ := hlookup cell.val hc
  unfold spanning_tree.Workspace.parent
  simp only [alloc.vec.Vec.index_slice_index]
  have hcellSlots : cell.val < w.edit_slots.val.length := by omega
  apply spec_bind (alloc.vec.Vec.index_usize_spec w.edit_slots cell hcellSlots)
  intro actual hactual
  have hactualSlot : actual = slot := by
    have hs := hslot
    rw [List.getElem?_eq_getElem hcellSlots] at hs
    exact hactual.trans (Option.some.inj hs)
  rw [hactualSlot]
  by_cases hmax : slot = core.num.Usize.MAX
  · simp only [hmax, ite_true]
    apply spec_mono (Slice.index_usize_spec published cell hpublished)
    intro value hvalue
    refine ⟨slot, hslot, Or.inl ⟨?_, ?_⟩⟩
    · simp [hmax]
    · rw [List.getElem?_eq_getElem hpublished]
      exact congrArg some hvalue.symm
  · simp only [hmax, ite_false]
    have hnotmax : slot.val ≠ Usize.max := by
      intro heq
      apply hmax
      apply UScalar.eq_of_val_eq
      simpa using heq
    have hbound : slot.val < w.edit_count.val := (hcases.resolve_left hnotmax).1
    have hi : slot.val < w.parents.val.length := by omega
    apply spec_mono (alloc.vec.Vec.index_usize_spec w.parents slot hi)
    intro value hvalue
    refine ⟨slot, hslot, Or.inr ⟨hbound, ?_⟩⟩
    rw [List.getElem?_eq_getElem hi]
    exact congrArg some hvalue.symm

 theorem mutation_validate_sweep_total
    (v : alloc.vec.Vec Usize) (root n start : Usize) (valid : Bool)
    (hn : n.val = v.val.length)
    (hp : ∀ x ∈ v.val.map (·.val), x < v.val.length)
    (hr : parentAt (v.val.map (·.val)) root.val = root.val)
    (hs : start.val ≤ n.val) :
    spanning_tree.Tree.validate_loop0 v root n start valid ⦃ result =>
      (result = true ↔ valid = true ∧
        ∀ j, start.val ≤ j → j < n.val →
          follow (v.val.map (·.val)) n.val j = root.val) ⦄ := by
  let good := fun j => follow (v.val.map (·.val)) n.val j = root.val
  let suffix := fun k => ∀ j, k ≤ j → j < n.val → good j
  let target := valid = true ∧ suffix start.val
  unfold spanning_tree.Tree.validate_loop0
  apply loop.spec_decr_nat
    (fun state : Usize × Bool => n.val - state.1.val)
    (fun state : Usize × Bool =>
      state.1.val ≤ n.val ∧ ((state.2 = true ∧ suffix state.1.val) ↔ target))
    (fun result : Bool => result = true ↔ target)
  · rintro ⟨current, flag⟩ ⟨hcurrent, hinv⟩
    dsimp only at hcurrent hinv ⊢
    unfold spanning_tree.Tree.validate_loop0.body
    by_cases hlt : current < n
    · simp only [hlt, ite_true]
      have hltNat : current.val < n.val := hlt
      cases flag with
      | false => simpa [target] using hinv
      | true =>
        simp only [ite_true]
        apply spec_bind (mutation_validate_walk_total v root n current 0#usize
          hn hp hr hlt (by simp))
        intro reached hreached
        apply spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
        intro current' hcurrent'
        have hnext : current'.val = current.val + 1 := by simpa using hcurrent'
        have hsplit : suffix current.val ↔ good current.val ∧ suffix current'.val := by
          constructor
          · intro h
            refine ⟨h _ (by omega) hlt, ?_⟩
            intro j hj hjn
            exact h j (by omega) hjn
          · rintro ⟨hhere, hrest⟩ j hj hjn
            by_cases heq : j = current.val
            · simpa [heq] using hhere
            · exact hrest j (by omega) hjn
        have hreach : reached = root ↔ good current.val := by
          constructor
          · intro heq
            simpa [good, heq] using hreached.symm
          · intro hgood
            apply UScalar.eq_of_val_eq
            simpa [good, hgood] using hreached
        simp only [spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        simpa [hsplit, hreach] using hinv
    · simp only [hlt, ite_false, spec_ok]
      have hempty : suffix current.val := by
        intro j hj hjn
        have : ¬ current.val < n.val := hlt
        omega
      simpa [hempty] using hinv
  · exact ⟨hs, Iff.rfl⟩

 theorem mutation_workspace_ensure_total
    (w : spanning_tree.Workspace) (cells edges : Usize) :
    spanning_tree.Workspace.ensure w cells edges ⦃ result =>
      result = (if cells.val ≤ w.path.val.length ∧ edges ≤ w.edge_capacity
        then core.result.Result.Ok ()
        else core.result.Result.Err topology.Error.InsufficientWorkspace) ⦄ := by
  simp only [spanning_tree.Workspace.ensure, UScalar.lt_equiv,
    UScalar.le_equiv, alloc.vec.Vec.len_val, alloc.vec.Vec.length]
  split
  · rename_i hc
    have hnot : ¬ cells.val ≤ w.path.val.length := by omega
    simp [hnot]
  · rename_i hc
    have hle : cells.val ≤ w.path.val.length := by omega
    split
    · rename_i he
      have hnot : ¬ edges.val ≤ w.edge_capacity.val := by omega
      simp [hle, hnot]
    · rename_i he
      have hleEdge : edges.val ≤ w.edge_capacity.val := by omega
      simp [hle, hleEdge]

 theorem mutation_reroot_invalid_index
    (t : spanning_tree.Tree) (newRoot : Usize) (w : spanning_tree.Workspace)
    (h : t.parents.val.length ≤ newRoot.val) :
    spanning_tree.Tree.reroot t newRoot w ⦃ result =>
      result = (core.result.Result.Err topology.Error.InvalidIndex, t, w) ⦄ := by
  simp [spanning_tree.Tree.reroot, h]

 theorem mutation_exchange_invalid_index
    (t : spanning_tree.Tree) (carrier : topology.Carrier)
    (child : Usize) (edge : topology.Edge) (w : spanning_tree.Workspace)
    (h : t.parents.val.length ≤ child.val) :
    spanning_tree.Tree.exchange t carrier child edge w ⦃ result =>
      result = (core.result.Result.Err topology.Error.InvalidIndex, t, w) ⦄ := by
  simp [spanning_tree.Tree.exchange, h]

 theorem mutation_exchange_root_rejected
    (t : spanning_tree.Tree) (carrier : topology.Carrier)
    (edge : topology.Edge) (w : spanning_tree.Workspace)
    (h : t.root.val < t.parents.val.length) :
    spanning_tree.Tree.exchange t carrier t.root edge w ⦃ result =>
      result = (core.result.Result.Err topology.Error.InvalidTransition, t, w) ⦄ := by
  simp [spanning_tree.Tree.exchange, Nat.not_le.mpr h]

 theorem mutation_workspace_path_valid (w : spanning_tree.Workspace)
    (path : alloc.vec.Vec Usize) (hw : WorkspaceValid w)
    (hlen : path.val.length = w.path.val.length) :
    WorkspaceValid { w with path := path } := by
  simpa only [WorkspaceValid, hlen] using hw

 theorem mutation_reroot_collect_total
    (v : alloc.vec.Vec Usize) (root n cell count : Usize)
    (w : spanning_tree.Workspace)
    (hn : n.val = v.val.length)
    (hw : WorkspaceValid w)
    (hcapacity : n.val ≤ w.path.val.length)
    (hcount : count.val ≤ n.val)
    (hpath : ∀ j, j < count.val →
      ∃ node, w.path.val[j]? = some node ∧ node.val < n.val) :
    spanning_tree.Tree.reroot_loop0 v root w n cell count ⦃ out =>
      WorkspaceValid out.1 ∧
      out.1.path.val.length = w.path.val.length ∧
      out.2.2.val ≤ n.val ∧
      (∀ j, j < out.2.2.val →
        ∃ node, out.1.path.val[j]? = some node ∧ node.val < n.val) ∧
      (n.val ≤ out.2.1.val ∨ n.val ≤ out.2.2.val ∨ out.2.1 = root) ⦄ := by
  unfold spanning_tree.Tree.reroot_loop0
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize × Usize => n.val - state.2.2.val)
    (fun state : spanning_tree.Workspace × Usize × Usize =>
      WorkspaceValid state.1 ∧
      state.1.path.val.length = w.path.val.length ∧
      state.2.2.val ≤ n.val ∧
      ∀ j, j < state.2.2.val →
        ∃ node, state.1.path.val[j]? = some node ∧ node.val < n.val)
    _
  · rintro ⟨scratch, current, used⟩ ⟨hvalid, hlength, hused, hnodes⟩
    dsimp only at hvalid hlength hused hnodes ⊢
    unfold spanning_tree.Tree.reroot_loop0.body
    by_cases hcell : current < n
    · simp only [hcell, ite_true]
      have hcellNat : current.val < n.val := hcell
      by_cases hroom : used < n
      · simp only [hroom, ite_true]
        have hroomNat : used.val < n.val := hroom
        by_cases hroot : current = root
        · simpa [hroot, hvalid, hlength, hused] using hnodes
        · have hbne : (current != root) = true := by simp [hroot]
          simp only [hbne, ite_true,
            alloc.vec.Vec.index_mut_slice_index]
          have hi : used.val < scratch.path.val.length := by omega
          apply spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.path used hi)
          rintro ⟨old, back⟩ ⟨_, hback⟩
          apply spec_bind (Usize.add_spec (x := used) (y := 1#usize) (by scalar_tac))
          intro used' hused'
          simp only [alloc.vec.Vec.index_slice_index]
          apply spec_bind (alloc.vec.Vec.index_usize_spec v current (by
            change current.val < v.val.length
            omega))
          intro next hnext
          subst back
          simp only [spec_ok]
          have husedval : used'.val = used.val + 1 := by simpa using hused'
          refine ⟨⟨mutation_workspace_path_valid scratch _ hvalid (by simp),
            by simpa using hlength, by omega, ?_⟩, by omega⟩
          intro j hj
          by_cases heq : j = used.val
          · refine ⟨current, ?_, hcell⟩
            simp [heq, hi]
          · obtain ⟨node, hnode, hbound⟩ := hnodes j (by omega)
            refine ⟨node, ?_, hbound⟩
            simpa [List.getElem?_set, heq, Ne.symm heq] using hnode
      · have hge : n.val ≤ used.val := Nat.le_of_not_lt hroom
        simpa [hroom, hvalid, hlength, hused, hge] using hnodes
    · have hge : n.val ≤ current.val := Nat.le_of_not_lt hcell
      simpa [hcell, hvalid, hlength, hused, hge] using hnodes
  · exact ⟨hw, rfl, hcount, hpath⟩

 theorem mutation_reroot_reverse_total
    (published path : alloc.vec.Vec Usize) (count index : Usize)
    (hstart : 1 ≤ index.val) (hindex : index.val ≤ count.val)
    (hcount : count.val ≤ path.val.length)
    (hpath : ∀ j, j < count.val →
      ∃ node, path.val[j]? = some node ∧ node.val < published.val.length) :
    spanning_tree.Tree.reroot_loop1 published path count index ⦃ result =>
      result.val.length = published.val.length ⦄ := by
  unfold spanning_tree.Tree.reroot_loop1
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize => count.val - state.2.val)
    (fun state : alloc.vec.Vec Usize × Usize =>
      state.1.val.length = published.val.length ∧
      1 ≤ state.2.val ∧ state.2.val ≤ count.val)
    (fun result : alloc.vec.Vec Usize => result.val.length = published.val.length)
  · rintro ⟨current, j⟩ ⟨hlen, hj, hjc⟩
    dsimp only at hlen hj hjc ⊢
    unfold spanning_tree.Tree.reroot_loop1.body
    by_cases hlt : j < count
    · simp only [hlt, ite_true]
      have hltNat : j.val < count.val := hlt
      apply spec_bind (Usize.sub_spec (x := j) (y := 1#usize) (by simpa using hj))
      intro prev hprev
      have hprevval : prev.val = j.val - 1 := by simpa using hprev.1
      have hprevlt : prev.val < path.val.length := by omega
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec path prev hprevlt)
      intro earlier hearlier
      have hjlt : j.val < path.val.length := by omega
      apply spec_bind (alloc.vec.Vec.index_usize_spec path j hjlt)
      intro node hnode
      obtain ⟨expected, hexpected, hbound⟩ := hpath j.val hlt
      have hsame : node = expected := by
        simpa [hnode, List.getElem?_eq_getElem hjlt] using hexpected
      have hnodebound : node.val < current.val.length := by simpa [hsame, hlen] using hbound
      simp only [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec current node hnodebound)
      rintro ⟨old, back⟩ ⟨_, hback⟩
      apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro j' hj'
      subst back
      simp only [spec_ok]
      have hj'val : j'.val = j.val + 1 := by simpa using hj'
      refine ⟨⟨by simpa using hlen, by omega, by omega⟩, by omega⟩
    · simpa [hlt] using hlen
  · exact ⟨rfl, hstart, hindex⟩

 theorem mutation_reroot_total_and_rejection
    (t : spanning_tree.Tree) (newRoot : Usize) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) :
    spanning_tree.Tree.reroot t newRoot w ⦃ out =>
      WorkspaceValid out.2.2 ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2.1 = t) ∧
      (out.1 = core.result.Result.Ok () →
        out.2.1.root = newRoot ∧
        out.2.1.parents.val.length = t.parents.val.length) ⦄ := by
  unfold spanning_tree.Tree.reroot
  by_cases hbad : newRoot ≥ alloc.vec.Vec.len t.parents
  · simp [hbad, hw]
  · simp only [hbad, ite_false]
    unfold spanning_tree.Workspace.ensure
    by_cases hcapacity : alloc.vec.Vec.len t.parents > alloc.vec.Vec.len w.path
    · simp [hcapacity, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        hw]
    · have hcap : t.parents.val.length ≤ w.path.val.length := by
        exact Nat.le_of_not_lt hcapacity
      have hedge : ¬ (0#usize > w.edge_capacity) := by scalar_tac
      simp only [hcapacity, hedge, ite_false,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with (mutation_reroot_collect_total t.parents t.root
        (alloc.vec.Vec.len t.parents) newRoot 0#usize w rfl hw hcap
        (by simp) (by simp))
        as ⟨scratch, cell, count, hscratch, hlength, hcount, hpath, hexit⟩
      by_cases hcell : t.parents.val.length ≤ cell.val
      · simp [hcell, hscratch]
      · by_cases hcountbad : t.parents.val.length ≤ count.val
        · simp [hcountbad, hscratch]
        · have hi : count.val < scratch.path.val.length := by omega
          have hcellGuard : ¬ cell ≥ alloc.vec.Vec.len t.parents := hcell
          have hcountGuard : ¬ count ≥ alloc.vec.Vec.len t.parents := hcountbad
          simp only [hcellGuard, hcountGuard, ite_false]
          step with (alloc.vec.Vec.index_mut_usize_spec scratch.path count hi)
            as ⟨old, back, hold, hback⟩
          step with (Usize.add_spec (x := count) (y := 1#usize) (by
            have hn := t.parents.property
            scalar_tac)) as ⟨count', hcount'⟩
          rw [hback]
          have hcountval : count'.val = count.val + 1 := by simpa using hcount'
          have hcellbound : cell.val < t.parents.val.length := by omega
          have hnewpath : ∀ j, j < count'.val →
              ∃ node, (scratch.path.set count cell).val[j]? = some node ∧
                node.val < t.parents.val.length := by
            intro j hj
            by_cases heq : j = count.val
            · exact ⟨cell, by simp [heq, hi], hcellbound⟩
            · obtain ⟨node, hnode, hbound⟩ := hpath j (by omega)
              exact ⟨node, by simpa [List.getElem?_set, heq, Ne.symm heq] using hnode,
                hbound⟩
          step with (mutation_reroot_reverse_total t.parents
            (scratch.path.set count cell) count' 1#usize (by simp)
            (by simp; omega) (by simp; omega) hnewpath) as ⟨reversed, hrev⟩
          have hrootbound : newRoot.val < reversed.val.length := by
            have hrootNat : ¬ t.parents.val.length ≤ newRoot.val := hbad
            omega
          step with (alloc.vec.Vec.index_mut_usize_spec reversed newRoot hrootbound)
            as ⟨oldRoot, backRoot, holdRoot, hbackRoot⟩
          rw [hbackRoot]
          have hfinal := mutation_workspace_path_valid scratch
            (scratch.path.set count cell) hscratch (by simp)
          simpa [hrev] using hfinal

 theorem mutation_carrier_len_total (c : topology.Carrier) (hc : CarrierValid c) :
    topology.Carrier.len c ⦃ result => result.val = cellCount c ⦄ := by
  unfold topology.Carrier.len
  apply spec_mono (Usize.sub_spec (x := alloc.vec.Vec.len c.offsets)
    (y := 1#usize) (by
      have := hc.1
      simp only [cellCount] at this
      simp only [alloc.vec.Vec.len_val]
      scalar_tac))
  intro result hresult
  simpa [cellCount] using hresult.1

 theorem mutation_carrier_offsets_mono (c : topology.Carrier) (hc : CarrierValid c)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ cellCount c) :
    (offsets c)[i]?.getD 0 ≤ (offsets c)[j]?.getD 0 := by
  induction j, hij using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ k hik ih =>
    have hk : k < cellCount c := by omega
    exact Nat.le_trans (ih (by omega)) (hc.2.2.2.1 k hk)

 theorem mutation_carrier_offsets_bound (c : topology.Carrier) (hc : CarrierValid c)
    (i : Nat) (hi : i ≤ cellCount c) :
    (offsets c)[i]?.getD 0 ≤ (neighbors c).length := by
  have h := mutation_carrier_offsets_mono c hc i (cellCount c) hi (Nat.le_refl _)
  simpa [hc.2.2.1] using h

 theorem mutation_carrier_scan_total (target : Usize) (values : Slice Usize)
    (start : Usize) (hstart : start.val ≤ values.val.length)
    (hprefix : ∀ j, j < start.val → values.val[j]? ≠ some target) :
    topology.Carrier.contains_edge_loop target values start ⦃ result =>
      result.val ≤ values.val.length ∧
      (∀ j, j < result.val → values.val[j]? ≠ some target) ∧
      (result.val < values.val.length → values.val[result.val]? = some target) ⦄ := by
  unfold topology.Carrier.contains_edge_loop
  apply loop.spec_decr_nat
    (fun i : Usize => values.val.length - i.val)
    (fun i : Usize => i.val ≤ values.val.length ∧
      ∀ j, j < i.val → values.val[j]? ≠ some target)
    _
  · intro current hcurrent
    unfold topology.Carrier.contains_edge_loop.body
    by_cases hlt : current < Slice.len values
    · simp only [hlt, ite_true]
      have hltNat : current.val < values.val.length := hlt
      apply spec_bind (Slice.index_usize_spec values current hlt)
      intro value hvalue
      by_cases hne : value ≠ target
      · have hbne : (value != target) = true := by simp [hne]
        simp only [hbne, ite_true]
        apply spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
        intro next hnext
        have hnextval : next.val = current.val + 1 := by simpa using hnext
        simp only [spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        intro j hj
        by_cases heq : j = current.val
        · subst j
          rw [List.getElem?_eq_getElem hlt]
          intro heq
          exact hne (hvalue.trans (Option.some.inj heq))
        · exact hcurrent.2 j (by omega)
      · have heq : value = target := Classical.not_not.mp hne
        simp only [heq, bne_self_eq_false, Bool.false_eq_true, ite_false, spec_ok]
        refine ⟨hcurrent.1, hcurrent.2, ?_⟩
        intro _
        rw [List.getElem?_eq_getElem hlt]
        exact congrArg some (hvalue.symm.trans heq)
    · simp only [hlt, ite_false, spec_ok]
      exact ⟨hcurrent.1, hcurrent.2, fun h => False.elim (hlt h)⟩
  · exact ⟨hstart, hprefix⟩

 theorem mutation_clear_edits_total
    (w : spanning_tree.Workspace) (hw : WorkspaceValid w) :
    spanning_tree.Workspace.clear_edits w ⦃ result =>
      WorkspaceValid result ∧ result.edit_count = 0#usize ∧
      result.seen = w.seen ∧ result.frames = w.frames ∧
      result.path = w.path ∧ result.parents = w.parents ∧
      result.incoming = w.incoming ∧ result.edit_nodes = w.edit_nodes ∧
      result.edge_capacity = w.edge_capacity ∧
      (∀ j, j < w.path.val.length →
        result.edit_slots.val[j]? = some core.num.Usize.MAX) ⦄ := by
  rcases hw with ⟨hseen, hframes, hparents, hincoming, hslots, hnodes,
    hcount, hnodup, hforward, hlookup⟩
  have hloop : spanning_tree.Workspace.clear_edits_loop w 0#usize ⦃ out =>
      ∃ slots : alloc.vec.Vec Usize,
        out = (w.seen, w.frames, w.path, w.parents, w.incoming, slots,
          w.edit_nodes, w.edge_capacity) ∧
        slots.val.length = w.path.val.length ∧
        ∀ j, j < w.path.val.length → slots.val[j]? = some core.num.Usize.MAX ⦄ := by
    unfold spanning_tree.Workspace.clear_edits_loop
    apply loop.spec_decr_nat
      (fun state : spanning_tree.Workspace × Usize => w.edit_count.val - state.2.val)
      (fun state : spanning_tree.Workspace × Usize =>
        state.2.val ≤ w.edit_count.val ∧
        ∃ slots : alloc.vec.Vec Usize,
          state.1 = { w with edit_slots := slots } ∧
          slots.val.length = w.path.val.length ∧
          ∀ j, j < w.path.val.length →
            ∃ slot, slots.val[j]? = some slot ∧
              (slot.val = Usize.max ∨
                (state.2.val ≤ slot.val ∧ slot.val < w.edit_count.val ∧
                  ∃ node, w.edit_nodes.val[slot.val]? = some node ∧ node.val = j)))
      _
    · rintro ⟨scratch, i⟩ ⟨hi, slots, rfl, hlen, hremaining⟩
      dsimp only at hi hlen hremaining ⊢
      unfold spanning_tree.Workspace.clear_edits_loop.body
      by_cases hlt : i < w.edit_count
      · simp only [hlt, ite_true, alloc.vec.Vec.index_slice_index]
        have hltNat : i.val < w.edit_count.val := hlt
        have hibound : i.val < w.edit_nodes.val.length := by omega
        apply spec_bind (alloc.vec.Vec.index_usize_spec w.edit_nodes i hibound)
        intro cell hcell
        obtain ⟨expected, hexpected, hcellbound, oldSlot, holdSlot, holdIndex⟩ :=
          hforward i.val hlt
        have hcellEq : cell = expected := by
          simpa [List.getElem?_eq_getElem hibound, ← hcell] using hexpected
        have hcellcap : cell.val < w.path.val.length := by simpa [hcellEq] using hcellbound
        have hcellslots : cell.val < slots.val.length := by omega
        simp only [alloc.vec.Vec.index_mut_slice_index]
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec slots cell hcellslots)
        rintro ⟨old, back⟩ ⟨_, hback⟩
        apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i' hi'
        have hinext : i'.val = i.val + 1 := by simpa using hi'
        subst back
        simp only [spec_ok]
        refine ⟨⟨by omega, slots.set cell core.num.Usize.MAX, rfl, by simpa using hlen, ?_⟩,
          by omega⟩
        intro j hj
        by_cases hsame : j = cell.val
        · refine ⟨core.num.Usize.MAX, ?_, Or.inl (by simp)⟩
          simp [hsame, hcellslots]
        · obtain ⟨slot, hslot, hmax | hactive⟩ := hremaining j hj
          · refine ⟨slot, ?_, Or.inl hmax⟩
            simpa [List.getElem?_set, hsame, Ne.symm hsame] using hslot
          · refine ⟨slot, ?_, Or.inr ⟨?_, hactive.2.1, hactive.2.2⟩⟩
            · simpa [List.getElem?_set, hsame, Ne.symm hsame] using hslot
            · have hne : slot.val ≠ i.val := by
                intro heq
                obtain ⟨node, hnode, hnodeval⟩ := hactive.2.2
                have hn : node = expected := by
                  rw [heq, hexpected] at hnode
                  exact Option.some.inj hnode.symm
                apply hsame
                simpa [hn, hcellEq] using hnodeval.symm
              omega
      · simp only [hlt, ite_false, spec_ok]
        refine ⟨slots, rfl, hlen, ?_⟩
        intro j hj
        obtain ⟨slot, hslot, hmax | hactive⟩ := hremaining j hj
        · have heq : slot = core.num.Usize.MAX := by
            apply UScalar.eq_of_val_eq
            simpa using hmax
          simpa [heq] using hslot
        · have hge : w.edit_count.val ≤ i.val := Nat.le_of_not_lt hlt
          omega
    · refine ⟨by simp, w.edit_slots, rfl, hslots, ?_⟩
      intro j hj
      obtain ⟨slot, hslot, hmax | hactive⟩ := hlookup j hj
      · exact ⟨slot, hslot, Or.inl hmax⟩
      · exact ⟨slot, hslot, Or.inr ⟨by simp, hactive⟩⟩
  unfold spanning_tree.Workspace.clear_edits
  apply spec_bind hloop
  rintro out ⟨slots, rfl, hlen, hall⟩
  apply (spec_ok _).mpr
  constructor
  · unfold WorkspaceValid
    refine ⟨hseen, hframes, hparents, hincoming, hlen, hnodes, by simp,
      by simp, by simp, ?_⟩
    intro node hnode
    exact ⟨core.num.Usize.MAX, hall node hnode, Or.inl (by simp)⟩
  · simpa using hall

end Labyrinth
