module
public import LabyrinthCore.MutationReroot
public import LabyrinthCore.MutationValidator

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_first_path_distinct (p : List Nat) (start root k : Nat)
    (hreach : follow p k start = root)
    (hfirst : ∀ j, j < k → follow p j start ≠ root) :
    ∀ i j, i ≤ k → j ≤ k → follow p i start = follow p j start → i = j := by
  have hordered : ∀ i j, i < j → j ≤ k → follow p i start ≠ follow p j start := by
    intro i j hij hj heq
    apply hfirst (k - j + i) (by omega)
    rw [mutation_follow_add, heq, ← mutation_follow_add, Nat.sub_add_cancel hj]
    exact hreach
  intro i j hi hj heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hordered i j hlt hj heq
  · exact hordered j i hgt hi heq.symm

 theorem mutation_parent_edges_connected (before after : List Nat)
    (hlen : after.length = before.length)
    (hedges : ∀ u v, parentEdge after u v ↔ parentEdge before u v)
    (hconnected : (constructorParentGraph before).Connected) :
    (constructorParentGraph after).Connected := by
  let hom : constructorParentGraph before →g constructorParentGraph after := {
    toFun := fun u => ⟨u.val, by omega⟩
    map_rel' := by
      intro u v hadj
      apply (constructor_parentGraph_adj_iff after _ _).mpr
      apply (hedges u.val v.val).mpr
      exact (constructor_parentGraph_adj_iff before u v).mp hadj }
  apply hconnected.map hom
  intro v
  exact ⟨⟨v.val, by omega⟩, Fin.ext rfl⟩

 theorem mutation_rooted_nonroot_parent_ne (p : List Nat) (root u : Nat)
    (hp : RootedTree p root) (hu : u < p.length) (hne : u ≠ root) :
    u ≠ parentAt p u := by
  intro heq
  have hfixed := mutation_follow_fixed p u heq.symm p.length
  exact hne (hfixed.symm.trans (hp.2.2.2 u hu))

 theorem mutation_tree_edge_carrier (c : topology.Carrier) (t : spanning_tree.Tree)
    (hc : CarrierValid c) (ht : TreeValid c t) (u v : Nat)
    (he : parentEdge (parents t) u v) : carrierEdge c u v := by
  obtain ⟨hu, hv, hne, huv | hvu⟩ := he
  · have hup : parentAt (parents t) u = v := by simp [parentAt, huv]
    have hnr : u ≠ t.root.val := by
      intro heq
      have hr := ht.2.1.2.1
      rw [← heq, huv] at hr
      exact hne (Option.some.inj hr).symm
    simpa only [hup] using ht.2.2 u hu hnr
  · have hvp : parentAt (parents t) v = u := by simp [parentAt, hvu]
    have hnr : v ≠ t.root.val := by
      intro heq
      have hr := ht.2.1.2.1
      rw [← heq, hvu] at hr
      exact hne (Option.some.inj hr)
    apply (mutation_carrier_symmetric c hc v u).mp
    simpa only [hvp] using ht.2.2 v hv hnr

 theorem mutation_reroot_model_preserves
    (c : topology.Carrier) (t result : spanning_tree.Tree) (newRoot : Usize) (k : Nat)
    (hc : CarrierValid c) (ht : TreeValid c t)
    (hnew : newRoot.val < (parents t).length)
    (hroot : result.root = newRoot)
    (hlen : (parents result).length = (parents t).length)
    (hreach : follow (parents t) k newRoot.val = t.root.val)
    (hnewParent : (parents result)[newRoot.val]? = some newRoot.val)
    (hback : ∀ j, j < k →
      (parents result)[follow (parents t) (j + 1) newRoot.val]? =
        some (follow (parents t) j newRoot.val))
    (hoff : ∀ u, u < (parents t).length →
      (∀ j, j ≤ k → follow (parents t) j newRoot.val ≠ u) →
      (parents result)[u]? = (parents t)[u]?) :
    TreeValid c result ∧
      ∀ u v, parentEdge (parents result) u v ↔ parentEdge (parents t) u v := by
  let p := parents t
  let q := parents result
  let path := fun j => follow p j newRoot.val
  have hlenq : q.length = p.length := hlen
  have hpath : ∀ j, path j < p.length := fun j =>
    mutation_follow_bound p ht.2.1.2.2.1 j newRoot.val hnew
  have hforward : ∀ j, j < k → p[path j]? = some (path (j + 1)) := by
    intro j _
    change p[path j]? = some (follow p (j + 1) newRoot.val)
    rw [mutation_follow_next]
    simp only [← show path j = follow p j newRoot.val from rfl,
      parentAt, List.getElem?_eq_getElem (hpath j), Option.getD_some]
  have holdRoot : p[path k]? = some (path k) := by
    change (parents t)[follow (parents t) k newRoot.val]? =
      some (follow (parents t) k newRoot.val)
    rw [hreach]
    exact ht.2.1.2.1
  have hedges := mutation_path_reversal_edges p q path k hlen hforward holdRoot
    hnewParent hback hoff
  have hbounded : ∀ x ∈ q, x < q.length := by
    intro x hx
    obtain ⟨u, hu, hget⟩ := List.mem_iff_getElem.mp hx
    have hsome : q[u]? = some x := by simp [hu, hget]
    by_cases hon : ∃ j, j ≤ k ∧ path j = u
    · obtain ⟨j, hj, hju⟩ := hon
      cases j with
      | zero =>
        have he := hnewParent
        have huRoot : newRoot.val = u := hju
        have he' : q[u]? = some newRoot.val := by
          simpa only [huRoot] using he
        have hxRoot : x = newRoot.val := Option.some.inj (hsome.symm.trans he')
        rw [hxRoot, hlenq]
        exact hnew
      | succ j =>
        have he : q[path (j + 1)]? = some (path j) := hback j (by omega)
        rw [hju, hsome] at he
        have hxPath : x = path j := Option.some.inj he
        rw [hxPath, hlenq]
        exact hpath j
    · have hout := hoff u (by change u < p.length; omega) (fun j hj he => hon ⟨j, hj, he⟩)
      have hmem : x ∈ p := List.mem_of_getElem? (hout.symm.trans hsome)
      rw [hlenq]
      exact ht.2.1.2.2.1 x hmem
  have hconnected := mutation_parent_edges_connected p q hlen hedges
    (constructor_rooted_connected ht.2.1)
  have hrooted : RootedTree q newRoot.val := mutation_connected_rooted q newRoot.val
    (by rw [hlenq]; exact hnew) hnewParent hbounded hconnected
  refine ⟨⟨hlen.trans ht.1, ?_, ?_⟩, hedges⟩
  · simpa only [hroot] using hrooted
  · intro u hu hne
    have hneq : u ≠ parentAt q u := mutation_rooted_nonroot_parent_ne q newRoot.val u
      hrooted hu (by simpa only [hroot] using hne)
    have hv := mutation_parentAt_bound q hbounded u hu
    apply mutation_tree_edge_carrier c t hc ht u (parentAt q u)
    apply (hedges u (parentAt q u)).mp
    have huq : u < q.length := hu
    exact ⟨hu, hv, hneq, Or.inl (by
      simp only [parentAt, List.getElem?_eq_getElem huq, Option.getD_some])⟩

 theorem mutation_reroot_success
    (c : topology.Carrier) (t : spanning_tree.Tree) (newRoot : Usize)
    (w : spanning_tree.Workspace) (hc : CarrierValid c) (ht : TreeValid c t)
    (hw : WorkspaceValid w) (hnew : newRoot.val < t.parents.val.length)
    (hcapacity : t.parents.val.length ≤ w.path.val.length) :
    spanning_tree.Tree.reroot t newRoot w ⦃ out =>
      out.1 = core.result.Result.Ok () ∧
      TreeValid c out.2.1 ∧ out.2.1.root = newRoot ∧
      WorkspaceValid out.2.2 ∧
      ∀ u v, parentEdge (parents out.2.1) u v ↔ parentEdge (parents t) u v ⦄ := by
  classical
  let p := parents t
  have hnewp : newRoot.val < p.length := by simpa [p, parents] using hnew
  have hexists : ∃ k, follow p k newRoot.val = t.root.val :=
    ⟨p.length, ht.2.1.2.2.2 newRoot.val hnewp⟩
  let k := Nat.find hexists
  have hreach : follow p k newRoot.val = t.root.val := Nat.find_spec hexists
  have hfirst : ∀ j, j < k → follow p j newRoot.val ≠ t.root.val :=
    fun j hj => Nat.find_min hexists hj
  obtain ⟨small, hsmall, hsmallReach⟩ := mutation_first_root_before_size p t.root.val
    newRoot.val ht.2.1.2.2.1 hnewp hexists
  have hk : k < t.parents.val.length := by
    have hle : k ≤ small := Nat.find_min' hexists hsmallReach
    simp only [p, parents, List.length_map] at hsmall
    omega
  have hdistinct := mutation_first_path_distinct p newRoot.val t.root.val k hreach hfirst
  have hpathBound : ∀ j, follow p j newRoot.val < t.parents.val.length := by
    intro j
    simpa only [p, parents, List.length_map] using
      mutation_follow_bound p ht.2.1.2.2.1 j newRoot.val hnewp
  unfold spanning_tree.Tree.reroot
  have hguard : ¬ newRoot ≥ alloc.vec.Vec.len t.parents := Nat.not_le.mpr hnew
  simp only [hguard, ite_false]
  apply spec_bind (mutation_workspace_ensure_total w (alloc.vec.Vec.len t.parents) 0#usize)
  intro ensured hensured
  have hensuredOk : ensured = core.result.Result.Ok () := by
    simpa [hcapacity] using hensured
  simp only [hensuredOk, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (mutation_reroot_collect_exact t.parents t.root
    (alloc.vec.Vec.len t.parents) newRoot w k rfl
    (by simpa only [p, parents, List.length_map] using ht.2.1.2.2.1)
    hnew hreach hfirst hk hw hcapacity)
  rintro ⟨scratch, cell, count⟩ ⟨hscratch, hlength, hcell, hcount, hnodes⟩
  change (if cell ≥ alloc.vec.Vec.len t.parents then
      Result.ok (core.result.Result.Err topology.Error.InvalidTree, t, scratch)
    else if count ≥ alloc.vec.Vec.len t.parents then
      Result.ok (core.result.Result.Err topology.Error.InvalidTree, t, scratch)
    else do
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice Usize) scratch.path count
      let count' ← count + 1#usize
      let reversed ← spanning_tree.Tree.reroot_loop1 t.parents (back cell) count' 1#usize
      let (_, backRoot) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice Usize) reversed newRoot
      Result.ok (core.result.Result.Ok (),
        { parents := backRoot newRoot, root := newRoot },
        { scratch with path := back cell })) ⦃ _ ⦄
  dsimp only at hscratch hlength hcell hcount hnodes ⊢
  have hcellBound : cell.val < t.parents.val.length := by
    rw [hcell]
    simpa only [parents, List.length_map] using ht.2.1.1
  have hcellGuard : ¬ cell ≥ alloc.vec.Vec.len t.parents := Nat.not_le.mpr hcellBound
  have hcountGuard : ¬ count ≥ alloc.vec.Vec.len t.parents := by
    change ¬ t.parents.val.length ≤ count.val
    omega
  simp only [hcellGuard, hcountGuard, ite_false, alloc.vec.Vec.index_mut_slice_index]
  have hcountBound : count.val < scratch.path.val.length := by omega
  apply spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.path count hcountBound)
  rintro ⟨old, back⟩ ⟨_, hback⟩
  apply spec_bind (Usize.add_spec (x := count) (y := 1#usize) (by
    have := t.parents.property
    scalar_tac))
  intro count' hcount'
  have hcountVal : count'.val = k + 1 := by simpa [hcount] using hcount'
  subst back
  let path := scratch.path.set count cell
  have hpath : ∀ j, j ≤ k → ∃ node, path.val[j]? = some node ∧
      node.val = follow p j newRoot.val := by
    intro j hj
    by_cases heq : j = k
    · refine ⟨cell, ?_, ?_⟩
      · simp [path, heq, ← hcount, hcountBound]
      · simpa only [heq, hcell] using hreach.symm
    · obtain ⟨node, hnode, hnodeval⟩ := hnodes j (by omega)
      exact ⟨node, by simpa [path, List.getElem?_set, hcount, heq, Ne.symm heq] using hnode,
        hnodeval⟩
  have hbounded : ∀ i, i < count'.val → ∀ node,
      path.val[i]? = some node → node.val < t.parents.val.length := by
    intro i hi node hnode
    obtain ⟨expected, hexpected, hval⟩ := hpath i (by omega)
    have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
    simpa only [he, hval] using hpathBound i
  have hunique : ∀ i j, i < count'.val → j < count'.val → ∀ x y,
      path.val[i]? = some x → path.val[j]? = some y → x.val = y.val → i = j := by
    intro i j hi hj x y hx hy he
    obtain ⟨x', hx', hxval⟩ := hpath i (by omega)
    obtain ⟨y', hy', hyval⟩ := hpath j (by omega)
    have hxe : x = x' := Option.some.inj (hx.symm.trans hx')
    have hye : y = y' := Option.some.inj (hy.symm.trans hy')
    apply hdistinct i j (by omega) (by omega)
    simpa only [hxe, hye, hxval, hyval] using he
  apply spec_bind (mutation_reroot_reverse_exact t.parents path count'
    (by omega) (by simp [path]; omega) hbounded hunique)
  rintro reversed ⟨hlen, hassigned, hunchanged⟩
  have hrootBound : newRoot.val < reversed.val.length := by omega
  apply spec_bind (alloc.vec.Vec.index_mut_usize_spec reversed newRoot hrootBound)
  rintro ⟨oldRoot, backRoot⟩ ⟨_, hbackRoot⟩
  subst backRoot
  let result : spanning_tree.Tree := {
    parents := reversed.set newRoot newRoot, root := newRoot }
  have hfinalLen : (parents result).length = (parents t).length := by
    simpa [result, parents] using hlen
  have hfinalRoot : (parents result)[newRoot.val]? = some newRoot.val := by
    simp [result, parents, hrootBound]
  have hfinalBack : ∀ j, j < k →
      (parents result)[follow p (j + 1) newRoot.val]? =
        some (follow p j newRoot.val) := by
    intro j hj
    obtain ⟨node, hnode, hnodeval⟩ := hpath (j + 1) (by omega)
    obtain ⟨prev, hprev, hprevval⟩ := hpath j (by omega)
    have hassignedHere := hassigned (j + 1) (by omega) (by omega) node prev hnode
      (by simpa using hprev)
    have hne : node.val ≠ newRoot.val := by
      intro he
      have hepath : follow p (j + 1) newRoot.val = follow p 0 newRoot.val := by
        simpa only [follow] using hnodeval.symm.trans he
      have := hdistinct (j + 1) 0 (by omega) (by omega) hepath
      omega
    simp [result, parents, ← hnodeval, Ne.symm hne, hassignedHere, hprevval]
  have hfinalOff : ∀ u, u < p.length →
      (∀ j, j ≤ k → follow p j newRoot.val ≠ u) →
      (parents result)[u]? = p[u]? := by
    intro u hu hoff
    have hne : newRoot.val ≠ u := hoff 0 (by omega)
    have hunchangedHere := hunchanged u (by simpa only [p, parents, List.length_map] using hu)
      (by
        intro i _ hi node hnode
        obtain ⟨expected, hexpected, hval⟩ := hpath i (by omega)
        have he : node = expected := Option.some.inj (hnode.symm.trans hexpected)
        simpa only [he, hval] using hoff i (by omega))
    simp [result, p, parents, hne, hunchangedHere]
  obtain ⟨hvalid, hedges⟩ := mutation_reroot_model_preserves c t result newRoot k hc ht
    hnewp rfl hfinalLen hreach hfinalRoot hfinalBack hfinalOff
  apply (spec_ok _).mpr
  exact ⟨rfl, hvalid, rfl,
    mutation_workspace_path_valid scratch path hscratch (by simp [path]), hedges⟩

 theorem mutation_reroot_preserves
    (c : topology.Carrier) (t : spanning_tree.Tree) (newRoot : Usize)
    (w : spanning_tree.Workspace) (hc : CarrierValid c) (ht : TreeValid c t)
    (hw : WorkspaceValid w) :
    spanning_tree.Tree.reroot t newRoot w ⦃ out =>
      TreeValid c out.2.1 ∧ WorkspaceValid out.2.2 ∧
      (∀ u v, parentEdge (parents out.2.1) u v ↔ parentEdge (parents t) u v) ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2.1 = t) ∧
      (out.1 = core.result.Result.Ok () → out.2.1.root = newRoot) ∧
      (out.1 = core.result.Result.Ok () ↔
        newRoot.val < t.parents.val.length ∧ t.parents.val.length ≤ w.path.val.length) ⦄ := by
  by_cases hnew : newRoot.val < t.parents.val.length
  · by_cases hcapacity : t.parents.val.length ≤ w.path.val.length
    · apply spec_mono (mutation_reroot_success c t newRoot w hc ht hw hnew hcapacity)
      rintro out ⟨hok, hvalid, hroot, hwork, hedges⟩
      exact ⟨hvalid, hwork, hedges, by simp [hok], fun _ => hroot,
        by simp [hok, hnew, hcapacity]⟩
    · have hguard : ¬ newRoot ≥ alloc.vec.Vec.len t.parents := Nat.not_le.mpr hnew
      have hsmall : alloc.vec.Vec.len t.parents > alloc.vec.Vec.len w.path :=
        Nat.lt_of_not_ge hcapacity
      simp [spanning_tree.Tree.reroot, hguard, spanning_tree.Workspace.ensure, hsmall,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        ht, hw, hcapacity]
  · apply spec_mono (mutation_reroot_invalid_index t newRoot w (by omega))
    intro out hout
    simp [hout, ht, hw, hnew]

end Labyrinth
