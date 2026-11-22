module
public import LabyrinthCore.MutationAttach
public import LabyrinthCore.MutationAttachmentModel
public import LabyrinthCore.MutationWorkspaceBounds

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_attach_path_total
    (v : alloc.vec.Vec Usize) (w : spanning_tree.Workspace)
    (inside outside component : Usize) (k : Nat)
    (hw : WorkspaceValid w) (hcapacity : v.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin v.val.length w)
    (hbound : ∀ j, j ≤ k →
      (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] inside.val < v.val.length)
    (hreach : (mutationVirtualParent w (alloc.vec.Vec.deref v))^[k] inside.val = component.val)
    (hfirst : ∀ j, j < k →
      (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] inside.val ≠ component.val)
    (hdistinct : ∀ i j, i ≤ k → j ≤ k →
      (mutationVirtualParent w (alloc.vec.Vec.deref v))^[i] inside.val =
        (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] inside.val → i = j)
    (hk : k < v.val.length) :
    (do
      let (work1, cell, count) ← spanning_tree.Tree.attach_virtual_loop0 v w
        (alloc.vec.Vec.len v) component inside 0#usize
      if cell ≥ alloc.vec.Vec.len v then
        Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
      else if count ≥ alloc.vec.Vec.len v then
        Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
      else
        let (_, back) ← alloc.vec.Vec.index_mut_usize work1.path count
        let count1 ← count + 1#usize
        let work2 ← spanning_tree.Tree.attach_virtual_loop1 {work1 with path := back cell}
          count1 1#usize
        let work3 ← spanning_tree.Workspace.set_parent work2 inside outside
        Result.ok (core.result.Result.Ok (), work3)) ⦃ out =>
      out.1 = core.result.Result.Ok () ∧ WorkspaceValid out.2 ∧
      out.2.path.val.length = w.path.val.length ∧
      MutationOverlayWithin v.val.length out.2 ∧
      mutationVirtualParent out.2 (alloc.vec.Vec.deref v) inside.val = outside.val ∧
      (∀ j, j < k →
        mutationVirtualParent out.2 (alloc.vec.Vec.deref v)
          ((mutationVirtualParent w (alloc.vec.Vec.deref v))^[j + 1] inside.val) =
          (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] inside.val) ∧
      (∀ u, u < v.val.length →
        (∀ j, j ≤ k → (mutationVirtualParent w (alloc.vec.Vec.deref v))^[j] inside.val ≠ u) →
        mutationVirtualParent out.2 (alloc.vec.Vec.deref v) u =
          mutationVirtualParent w (alloc.vec.Vec.deref v) u) ⦄ := by
  let next := mutationVirtualParent w (alloc.vec.Vec.deref v)
  apply spec_bind (mutation_virtual_collect_exact v w (alloc.vec.Vec.len v) component inside k
    rfl hw hcapacity hbound hreach hfirst hk)
  rintro ⟨scratch, cell, count⟩ ⟨hvalid, hlength, hparents, hslots, hcell, hcount, hnodes⟩
  change (if cell ≥ alloc.vec.Vec.len v then
      Result.ok (core.result.Result.Err topology.Error.InvalidTree, scratch)
    else if count ≥ alloc.vec.Vec.len v then
      Result.ok (core.result.Result.Err topology.Error.InvalidTree, scratch)
    else do
      let (_, back) ← alloc.vec.Vec.index_mut_usize scratch.path count
      let count1 ← count + 1#usize
      let work2 ← spanning_tree.Tree.attach_virtual_loop1 {scratch with path := back cell}
        count1 1#usize
      let work3 ← spanning_tree.Workspace.set_parent work2 inside outside
      Result.ok (core.result.Result.Ok (), work3)) ⦃ _ ⦄
  dsimp only at hvalid hlength hparents hslots hcell hcount hnodes ⊢
  have hcellBound : cell.val < v.val.length := by
    rw [hcell, ← hreach]
    exact hbound k (by omega)
  have hcellGuard : ¬ cell ≥ alloc.vec.Vec.len v := Nat.not_le.mpr hcellBound
  have hcountGuard : ¬ count ≥ alloc.vec.Vec.len v := by
    change ¬ v.val.length ≤ count.val
    omega
  simp only [hcellGuard, hcountGuard, ite_false]
  have hcountBound : count.val < scratch.path.val.length := by omega
  apply spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.path count hcountBound)
  rintro ⟨old, back⟩ ⟨_, hback⟩
  apply spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
    have := v.property
    scalar_tac))
  intro count' hcount'
  have hcountVal : count'.val = k + 1 := by simpa [hcount] using hcount'
  subst back
  let path := scratch.path.set count cell
  let prepared : spanning_tree.Workspace := {scratch with path := path}
  have hprepared : WorkspaceValid prepared := mutation_workspace_path_valid scratch path hvalid (by simp [path])
  have hpreparedLen : prepared.path.val.length = w.path.val.length := by simpa [prepared, path] using hlength
  have hpreparedWithin : MutationOverlayWithin v.val.length prepared := by
    intro u hnu hu
    change scratch.edit_slots.val[u]? = some core.num.Usize.MAX
    rw [hslots]
    exact hwithin u hnu (by simpa only [hpreparedLen] using hu)
  have hpreparedParent : ∀ u, mutationVirtualParent prepared (alloc.vec.Vec.deref v) u = next u := by
    intro u
    simp only [mutationVirtualParent, prepared, next, hparents, hslots]
  have hpath : ∀ j, j ≤ k → ∃ node, path.val[j]? = some node ∧ node.val = next^[j] inside.val := by
    intro j hj
    by_cases heq : j = k
    · refine ⟨cell, ?_, ?_⟩
      · simp [path, heq, ← hcount, hcountBound]
      · simpa only [heq, hcell] using hreach.symm
    · obtain ⟨node, hnode, hval⟩ := hnodes j (by omega)
      exact ⟨node, by simpa [path, List.getElem?_set, hcount, heq, Ne.symm heq] using hnode, hval⟩
  have hbounded : ∀ i, i < count'.val → ∀ node,
      prepared.path.val[i]? = some node → node.val < prepared.path.val.length := by
    intro i hi node hnode
    obtain ⟨expected, hexpected, hval⟩ := hpath i (by omega)
    have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
    rw [he, hval, hpreparedLen]
    exact lt_of_lt_of_le (hbound i (by omega)) hcapacity
  have hunique : ∀ i j, i < count'.val → j < count'.val → ∀ x y,
      prepared.path.val[i]? = some x → prepared.path.val[j]? = some y → x.val = y.val → i = j := by
    intro i j hi hj x y hx hy he
    obtain ⟨x', hx', hxval⟩ := hpath i (by omega)
    obtain ⟨y', hy', hyval⟩ := hpath j (by omega)
    have hxe : x = x' := Option.some.inj (hx.symm.trans hx')
    have hye : y = y' := Option.some.inj (hy.symm.trans hy')
    apply hdistinct i j (by omega) (by omega)
    simpa only [hxe, hye, hxval, hyval] using he
  have hnodeWithin : ∀ i, i < count'.val → ∀ node,
      prepared.path.val[i]? = some node → node.val < v.val.length := by
    intro i hi node hnode
    obtain ⟨expected, hexpected, hval⟩ := hpath i (by omega)
    have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
    simpa only [he, hval] using hbound i (by omega)
  apply spec_bind (spec_and
    (mutation_virtual_reverse_exact prepared (alloc.vec.Vec.deref v) count'
      hprepared (by omega) (by rw [hpreparedLen]; omega) hbounded hunique)
    (mutation_virtual_reverse_within v.val.length prepared count' hprepared hpreparedWithin
      (by rw [hpreparedLen]; exact hcapacity) (by omega)
      (by rw [hpreparedLen]; omega) hnodeWithin))
  rintro reversed ⟨⟨hrevValid, hrevPath, hbackward, hoff⟩, _, _, hrevWithin⟩
  have hinside : inside.val < reversed.path.val.length := by
    have hb := hbound 0 (by omega)
    simp only [Function.iterate_zero_apply] at hb
    rw [hrevPath, hpreparedLen]
    omega
  apply spec_bind (spec_and
    (mutation_workspace_set_parent_exact reversed inside outside (alloc.vec.Vec.deref v)
      hrevValid hinside)
    (mutation_set_parent_within v.val.length reversed inside outside hrevValid
      (by simpa only [Function.iterate_zero_apply] using hbound 0 (by omega))
      (by rw [hrevPath, hpreparedLen]; exact hcapacity) hrevWithin))
  rintro result ⟨⟨hresult, hresultPath, _, _, _, _, hupdate⟩, _, _, hresultWithin⟩
  apply (spec_ok _).mpr
  refine ⟨rfl, hresult, ?_, hresultWithin, ?_, ?_, ?_⟩
  · rw [hresultPath, hrevPath, hpreparedLen]
  · simpa using hupdate inside.val hinside
  · intro j hj
    obtain ⟨node, hnode, hnodeval⟩ := hpath (j + 1) (by omega)
    obtain ⟨prev, hprev, hprevval⟩ := hpath j (by omega)
    have hassigned := hbackward (j + 1) (by omega) (by omega) node prev hnode (by simpa using hprev)
    have hne : node.val ≠ inside.val := by
      intro he
      have hepath : next^[j + 1] inside.val = next^[0] inside.val := by
        simpa using hnodeval.symm.trans he
      have := hdistinct (j + 1) 0 (by omega) (by omega) hepath
      omega
    have hb : node.val < reversed.path.val.length := by
      rw [hrevPath]
      exact hbounded (j + 1) (by omega) node hnode
    change mutationVirtualParent result (alloc.vec.Vec.deref v) (next^[j + 1] inside.val) =
      next^[j] inside.val
    rw [← hnodeval, hupdate node.val hb]
    simp only [hne, ite_false, hassigned, hprevval]
  · intro u hu hout
    have hne : u ≠ inside.val := Ne.symm (hout 0 (by omega))
    have hb : u < reversed.path.val.length := by rw [hrevPath, hpreparedLen]; omega
    rw [hupdate u hb]
    simp only [hne, ite_false]
    rw [hoff u (by rw [hpreparedLen]; omega), hpreparedParent]
    intro i _ hi node hnode
    obtain ⟨expected, hexpected, hval⟩ := hpath i (by omega)
    have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
    simpa only [he, hval] using hout i (by omega)

 theorem mutation_attach_virtual_preserves
    (t : spanning_tree.Tree) (edge : topology.Edge) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin t.parents.val.length w)
    (hu : edge.u.val < t.parents.val.length) (hv : edge.v.val < t.parents.val.length)
    (hforest : MutationFunctionalForest t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)))
    (hrootBound : t.root.val < t.parents.val.length)
    (hrootFixed : mutationVirtualParent w (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val) :
    spanning_tree.Tree.attach_virtual t edge w ⦃ out =>
      WorkspaceValid out.2 ∧ out.2.path.val.length = w.path.val.length ∧
      MutationOverlayWithin t.parents.val.length out.2 ∧
      MutationFunctionalForest t.parents.val.length
        (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) ∧
      mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2 = w) ∧
      (out.1 = core.result.Result.Ok () → ∀ a b,
        mutationFunctionalEdge t.parents.val.length
          (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) a b ↔
        mutationFunctionalEdge t.parents.val.length
          (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)) a b ∨
          (a = edge.u.val ∧ b = edge.v.val) ∨ (b = edge.u.val ∧ a = edge.v.val)) ⦄ := by
  let n := t.parents.val.length
  let before := mutationVirtualParent w (alloc.vec.Vec.deref t.parents)
  have hbeforeBound := mutation_functional_forest_bounds n before hforest
  have hiterBound : ∀ j u, u < n → before^[j] u < n := by
    intro j
    induction j with
    | zero => exact fun _ h => h
    | succ j ih =>
      intro u hu
      simpa only [Function.iterate_succ_apply'] using hbeforeBound _ (ih u hu)
  have hpathSpec (inside outside component other : Usize)
      (hi : inside.val < n) (ho : outside.val < n)
      (hcomponent : MutationVirtualRootWitness before n inside.val component.val)
      (hother : MutationVirtualRootWitness before n outside.val other.val)
      (hdiff : component ≠ other) (hnotRoot : component ≠ t.root)
      (hedge : (inside = edge.u ∧ outside = edge.v) ∨
        (inside = edge.v ∧ outside = edge.u)) :
      (do
        let (work1, cell, count) ← spanning_tree.Tree.attach_virtual_loop0 t.parents w
          (alloc.vec.Vec.len t.parents) component inside 0#usize
        if cell ≥ alloc.vec.Vec.len t.parents then
          Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
        else if count ≥ alloc.vec.Vec.len t.parents then
          Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
        else
          let (_, back) ← alloc.vec.Vec.index_mut_usize work1.path count
          let count1 ← count + 1#usize
          let work2 ← spanning_tree.Tree.attach_virtual_loop1 {work1 with path := back cell}
            count1 1#usize
          let work3 ← spanning_tree.Workspace.set_parent work2 inside outside
          Result.ok (core.result.Result.Ok (), work3)) ⦃ out =>
        WorkspaceValid out.2 ∧ out.2.path.val.length = w.path.val.length ∧
        MutationOverlayWithin n out.2 ∧
        MutationFunctionalForest n (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) ∧
        mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
        (∀ error, out.1 = core.result.Result.Err error → out.2 = w) ∧
        (out.1 = core.result.Result.Ok () → ∀ a b,
          mutationFunctionalEdge n (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) a b ↔
          mutationFunctionalEdge n before a b ∨
            (a = edge.u.val ∧ b = edge.v.val) ∨
              (b = edge.u.val ∧ a = edge.v.val)) ⦄ := by
    obtain ⟨first, hfirst, hreach, hfixed, _⟩ := hcomponent
    obtain ⟨k, hk, hreachk, hminimal, hdistinct⟩ := mutation_functional_first_reach before n
      inside.val component.val hbeforeBound hi ⟨first, hreach⟩
    apply spec_mono (mutation_attach_path_total t.parents w inside outside component k
      hw hcapacity hwithin (fun j _ => hiterBound j inside.val hi) hreachk hminimal hdistinct hk)
    rintro out ⟨hok, hwork, hlen, hinside, hnew, hback, hoff⟩
    have hdiffVal : component.val ≠ other.val := fun he => hdiff (UScalar.eq_of_val_eq he)
    have hnotRootVal : t.root.val ≠ component.val := fun he => hnotRoot (UScalar.eq_of_val_eq he.symm)
    have hinsideNe : inside.val ≠ outside.val := by
      intro he
      apply hdiffVal
      apply mutation_fixed_reach_unique before outside.val component.val other.val
      · exact ⟨first, by simpa only [he] using hreach⟩
      · exact hfixed
      · obtain ⟨steps, _, hsteps, _, _⟩ := hother
        exact ⟨steps, hsteps⟩
      · exact hother.choose_spec.2.2.1
    have hforestAfter := mutation_functional_attach_preserves n before
      (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) inside.val outside.val
      component.val other.val k hforest hi ho hreachk hfixed hother hdiffVal hnew hback hoff
    have hrootAfter := mutation_functional_attach_fixed_root n before
      (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents)) inside.val component.val
      t.root.val k hrootBound hrootFixed hreachk hnotRootVal hoff
    have hedges := mutation_functional_attach_edges n before
      (mutationVirtualParent out.2 (alloc.vec.Vec.deref t.parents))
      (fun j => before^[j] inside.val) k outside.val hi ho hinsideNe
      (fun j _ => (Function.iterate_succ_apply' before j inside.val).symm)
      (by simpa only [hreachk] using hfixed) hnew hback hoff
    refine ⟨hwork, hlen, hinside, hforestAfter, hrootAfter, by simp [hok], ?_⟩
    intro _ a b
    rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hedges a b
    · have h := hedges a b
      simp only [Function.iterate_zero_apply] at h
      tauto
  unfold spanning_tree.Tree.attach_virtual
  apply spec_bind (mutation_virtual_root_total t edge.u w hw hcapacity)
  rintro first ⟨hfirst, _⟩
  cases first with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      hw, hwithin, hforest, hrootFixed]
  | Ok rootU =>
    have hrootU := hfirst rootU rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (mutation_virtual_root_total t edge.v w hw hcapacity)
    rintro second ⟨hsecond, _⟩
    cases second with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        hw, hwithin, hforest, hrootFixed]
    | Ok rootV =>
      have hrootV := hsecond rootV rfl
      simp only [bind_ok]
      by_cases heq : rootU = rootV
      · simp [heq, hw, hwithin, hforest, hrootFixed]
      · simp only [heq, ite_false]
        by_cases hglobal : rootU = t.root
        · simp only [hglobal, ite_true, bind_ok, alloc.vec.Vec.index_mut_slice_index]
          apply hpathSpec edge.v edge.u rootV t.root hv hu hrootV
            (by simpa only [hglobal] using hrootU)
            (by simpa only [hglobal] using Ne.symm heq)
            (by simpa only [hglobal] using Ne.symm heq) (Or.inr ⟨rfl, rfl⟩)
        · simp only [hglobal, ite_false, bind_ok, alloc.vec.Vec.index_mut_slice_index]
          exact hpathSpec edge.u edge.v rootU rootV hu hv hrootU hrootV heq hglobal
            (Or.inl ⟨rfl, rfl⟩)

end Labyrinth
