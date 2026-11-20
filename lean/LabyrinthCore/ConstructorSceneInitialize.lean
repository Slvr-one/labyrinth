module
public import LabyrinthCore.ConstructorContraction
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The extracted scene constructor initializes singleton union-find classes. -/
theorem constructor_scene_links_spec (n : Usize) (links : alloc.vec.Vec Usize)
    (hcapacity : n.val ≤ links.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop0 n links 0#usize) (fun output =>
      output.val.length = links.val.length ∧
      (∀ node : Usize, node.val < n.val → output.val[node.val]? = some node) ∧
      (∀ j, n.val ≤ j → output.val[j]? = links.val[j]?)) := by
  let invariant : alloc.vec.Vec Usize × Usize → Prop := fun state =>
    state.1.val.length = links.val.length ∧ state.2.val ≤ n.val ∧
    (∀ node : Usize, node.val < state.2.val → state.1.val[node.val]? = some node) ∧
    (∀ j, state.2.val ≤ j → state.1.val[j]? = links.val[j]?)
  unfold spanning_tree.Tree.scene_dfs_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize => n.val - state.2.val) invariant
  · rintro ⟨current, index⟩ hinv
    obtain ⟨hlen, hindex, hprefix, hsuffix⟩ := hinv
    dsimp only at hlen hindex hprefix hsuffix
    unfold spanning_tree.Tree.scene_dfs_loop0.body
    by_cases hmore : index < n
    · have hi : index.val < n.val := by simpa using hmore
      have hbound : index.val < current.val.length := by omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current index hbound)
      rintro ⟨old, back⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by simpa using hlen, by omega, ?_, ?_⟩, by omega⟩
      · intro node hnode
        by_cases he : node = index
        · subst node
          simp [alloc.vec.Vec.set, hbound]
        · have hne : node.val ≠ index.val := fun h => he ((UScalar.eq_equiv _ _).mpr h)
          simpa [alloc.vec.Vec.set, hne, Ne.symm hne] using hprefix node (by omega)
      · intro j hj
        have hne : j ≠ index.val := by omega
        simpa [alloc.vec.Vec.set, hne, Ne.symm hne] using hsuffix j (by omega)
    · have he : index.val = n.val := by
        have : ¬ index.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hlen, by simpa only [he] using hprefix, by simpa only [he] using hsuffix⟩
  · exact ⟨rfl, by simp, fun _ h => by simp at h, fun _ _ => rfl⟩

/-- Canonicalization is orientation-independent, including noncanonical input edges. -/
def constructorCanonicalEdge (edge : topology.Edge) : topology.Edge :=
  if edge.u ≤ edge.v then edge else { u := edge.v, v := edge.u }

theorem constructor_edge_new_spec (edge : topology.Edge) :
    WP.spec (topology.Edge.new edge.u edge.v)
      (fun output => output = constructorCanonicalEdge edge) := by
  cases edge with
  | mk u v =>
    unfold topology.Edge.new constructorCanonicalEdge
    split <;> simp

/-- The actual selected-edge initialization retains every required edge, in input order. -/
theorem constructor_scene_required_copy_spec (required : Slice topology.Edge)
    (selected : alloc.vec.Vec topology.Edge)
    (hcapacity : required.val.length ≤ selected.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected) (fun output =>
      output.val.length = selected.val.length ∧
      (∀ j, j < required.val.length →
        output.val[j]? = (required.val[j]?).map constructorCanonicalEdge) ∧
      (∀ j, required.val.length ≤ j → output.val[j]? = selected.val[j]?)) := by
  let invariant : Usize × alloc.vec.Vec topology.Edge → Prop := fun state =>
    state.2.val.length = selected.val.length ∧ state.1.val ≤ required.val.length ∧
    (∀ j, j < state.1.val →
      state.2.val[j]? = (required.val[j]?).map constructorCanonicalEdge) ∧
    (∀ j, state.1.val ≤ j → state.2.val[j]? = selected.val[j]?)
  unfold spanning_tree.Tree.scene_dfs_loop6
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec topology.Edge => required.val.length - state.1.val)
    invariant
  · rintro ⟨index, current⟩ hinv
    obtain ⟨hlen, hindex, hprefix, hsuffix⟩ := hinv
    dsimp only at hlen hindex hprefix hsuffix
    unfold spanning_tree.Tree.scene_dfs_loop6.body
    by_cases hmore : index < Slice.len required
    · have hi : index.val < required.val.length := by simpa using hmore
      have hbound : index.val < current.val.length := by omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (Slice.index_usize_spec required index hi)
      intro edge hedge
      have hlookup : required.val[index.val]? = some edge := by
        rw [List.getElem?_eq_getElem hi, hedge]
      apply WP.spec_bind (constructor_edge_new_spec edge)
      intro canonical hcanonical
      subst canonical
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current index hbound)
      rintro ⟨old, back⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := required.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by simpa using hlen, by omega, ?_, ?_⟩, by omega⟩
      · intro j hj
        by_cases he : j = index.val
        · subst j
          simp [alloc.vec.Vec.set, hbound, hlookup]
        · simpa [alloc.vec.Vec.set, he, Ne.symm he] using hprefix j (by omega)
      · intro j hj
        have he : j ≠ index.val := by omega
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hsuffix j (by omega)
    · have he : index.val = required.val.length := by
        have : ¬ index.val < required.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hlen, by simpa only [he] using hprefix, by simpa only [he] using hsuffix⟩
  · exact ⟨rfl, by simp, fun _ h => by simp at h, fun _ _ => rfl⟩

end Labyrinth
