module
public import LabyrinthCore.ConstructorContraction
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- One crossing original edge writes both directed quotient slots with that same original witness.
The hypotheses are storage/cursor bounds, not an assumption that the extracted fill succeeds. -/
theorem constructor_quotient_fill_crossing_spec
    (components : alloc.vec.Vec Usize) (edges : Slice topology.Edge) (index : Usize)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (next : alloc.vec.Vec Usize) (edge : topology.Edge) (u v a b : Usize)
    (hi : index.val < edges.val.length) (he : edges.val[index.val]? = some edge)
    (heu : edge.u.val < components.val.length) (hev : edge.v.val < components.val.length)
    (hu : components.val[edge.u.val]? = some u)
    (hv : components.val[edge.v.val]? = some v) (hne : u ≠ v)
    (hun : u.val < next.val.length) (hvn : v.val < next.val.length)
    (ha : next.val[u.val]? = some a) (hb : next.val[v.val]? = some b)
    (han : a.val < neighbors.val.length) (hbn : b.val < neighbors.val.length)
    (haw : a.val < witnesses.val.length) (hbw : b.val < witnesses.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop5.body components edges index neighbors witnesses next)
      (fun output => ∃ nextIndex nextA nextB : Usize,
        nextIndex.val = index.val + 1 ∧ nextA.val = a.val + 1 ∧ nextB.val = b.val + 1 ∧
        output = .cont (nextIndex, (neighbors.set a v).set b u,
          (witnesses.set a edge).set b edge, (next.set u nextA).set v nextB)) := by
  unfold spanning_tree.Tree.scene_dfs_loop5.body
  have hmore : index < Slice.len edges := by simpa using hi
  simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
    alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (Slice.index_usize_spec edges index hi)
  intro actualEdge heLookup
  have he' : edges.val[index.val]? = some actualEdge := by
    rw [List.getElem?_eq_getElem hi, heLookup]
  have heq : actualEdge = edge := Option.some.inj (he'.symm.trans he)
  rw [heq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.u heu)
  intro actualU huLookup
  have hu' : components.val[edge.u.val]? = some actualU := by
    rw [List.getElem?_eq_getElem heu, huLookup]
  have hueq : actualU = u := Option.some.inj (hu'.symm.trans hu)
  rw [hueq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.v hev)
  intro actualV hvLookup
  have hv' : components.val[edge.v.val]? = some actualV := by
    rw [List.getElem?_eq_getElem hev, hvLookup]
  have hveq : actualV = v := Option.some.inj (hv'.symm.trans hv)
  rw [hveq]
  simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, ite_true]
  have hfill : WP.spec (do
      let slotA ← next.index_usize u
      let (_, backNeighborA) ← neighbors.index_mut_usize slotA
      let (_, backWitnessA) ← witnesses.index_mut_usize slotA
      let (oldA, backA) ← next.index_mut_usize u
      let nextA ← oldA + 1#usize
      let slotB ← (backA nextA).index_usize v
      let (_, backNeighborB) ← (backNeighborA v).index_mut_usize slotB
      let (_, backWitnessB) ← (backWitnessA edge).index_mut_usize slotB
      let (oldB, backB) ← (backA nextA).index_mut_usize v
      let nextB ← oldB + 1#usize
      ok (backNeighborB u, backWitnessB edge, backB nextB))
      (fun filled => ∃ nextA nextB : Usize,
        nextA.val = a.val + 1 ∧ nextB.val = b.val + 1 ∧
        filled = ((neighbors.set a v).set b u, (witnesses.set a edge).set b edge,
          (next.set u nextA).set v nextB)) := by
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec next u hun)
    intro actualA haLookup
    have ha' : next.val[u.val]? = some actualA := by
      rw [List.getElem?_eq_getElem hun, haLookup]
    have haeq : actualA = a := Option.some.inj (ha'.symm.trans ha)
    rw [haeq]
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec neighbors a han)
    rintro ⟨oldNeighborA, backNeighborA⟩ ⟨_, rfl⟩
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec witnesses a haw)
    rintro ⟨oldWitnessA, backWitnessA⟩ ⟨_, rfl⟩
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec next u hun)
    rintro ⟨oldA, backA⟩ ⟨holdA, rfl⟩
    have holdA' : next.val[u.val]? = some oldA := by
      rw [List.getElem?_eq_getElem hun, holdA]
    have holdAEq : oldA = a := Option.some.inj (holdA'.symm.trans ha)
    rw [holdAEq]
    apply WP.spec_bind (Usize.add_spec (x := a) (y := 1#usize) (by
      have := neighbors.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro nextA hnextA
    have hnextA' : nextA.val = a.val + 1 := by simpa using hnextA
    have hvu : v.val ≠ u.val := by
      intro h
      exact hne ((UScalar.eq_equiv _ _).mpr h.symm)
    have hvn' : v.val < (next.set u nextA).val.length := by simpa using hvn
    have hb' : (next.set u nextA).val[v.val]? = some b := by
      simpa [alloc.vec.Vec.set, hvu, Ne.symm hvu] using hb
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec (next.set u nextA) v hvn')
    intro actualB hbLookup
    have hbl : (next.set u nextA).val[v.val]? = some actualB := by
      rw [List.getElem?_eq_getElem hvn', hbLookup]
    have hbeq : actualB = b := Option.some.inj (hbl.symm.trans hb')
    rw [hbeq]
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (neighbors.set a v) b (by
      simpa using hbn))
    rintro ⟨oldNeighborB, backNeighborB⟩ ⟨_, rfl⟩
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (witnesses.set a edge) b (by
      simpa using hbw))
    rintro ⟨oldWitnessB, backWitnessB⟩ ⟨_, rfl⟩
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (next.set u nextA) v hvn')
    rintro ⟨oldB, backB⟩ ⟨holdB, rfl⟩
    have holdB' : (next.set u nextA).val[v.val]? = some oldB := by
      rw [List.getElem?_eq_getElem hvn', holdB]
    have holdBEq : oldB = b := Option.some.inj (holdB'.symm.trans hb')
    rw [holdBEq]
    apply WP.spec_bind (Usize.add_spec (x := b) (y := 1#usize) (by
      have := neighbors.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro nextB hnextB
    apply (WP.spec_ok _).mpr
    exact ⟨nextA, nextB, hnextA', by simpa using hnextB, rfl⟩
  apply WP.spec_bind hfill
  intro filled hfilled
  obtain ⟨nextA, nextB, hnextA', hnextB', hfilledEq⟩ := hfilled
  rw [hfilledEq]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
    have := edges.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextIndex hnextIndex
  apply (WP.spec_ok _).mpr
  exact ⟨nextIndex, nextA, nextB, by simpa using hnextIndex, hnextA', hnextB', rfl⟩

/-- Edges internal to a required component consume no quotient slot. -/
theorem constructor_quotient_fill_internal_spec
    (components : alloc.vec.Vec Usize) (edges : Slice topology.Edge) (index : Usize)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (next : alloc.vec.Vec Usize) (edge : topology.Edge) (component : Usize)
    (hi : index.val < edges.val.length) (he : edges.val[index.val]? = some edge)
    (heu : edge.u.val < components.val.length) (hev : edge.v.val < components.val.length)
    (hu : components.val[edge.u.val]? = some component)
    (hv : components.val[edge.v.val]? = some component) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop5.body components edges index neighbors witnesses next)
      (fun output => ∃ nextIndex : Usize, nextIndex.val = index.val + 1 ∧
        output = .cont (nextIndex, neighbors, witnesses, next)) := by
  unfold spanning_tree.Tree.scene_dfs_loop5.body
  have hmore : index < Slice.len edges := by simpa using hi
  simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (Slice.index_usize_spec edges index hi)
  intro actualEdge heLookup
  have he' : edges.val[index.val]? = some actualEdge := by
    rw [List.getElem?_eq_getElem hi, heLookup]
  have heq : actualEdge = edge := Option.some.inj (he'.symm.trans he)
  rw [heq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.u heu)
  intro actualU huLookup
  have hu' : components.val[edge.u.val]? = some actualU := by
    rw [List.getElem?_eq_getElem heu, huLookup]
  have hueq : actualU = component := Option.some.inj (hu'.symm.trans hu)
  rw [hueq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.v hev)
  intro actualV hvLookup
  have hv' : components.val[edge.v.val]? = some actualV := by
    rw [List.getElem?_eq_getElem hev, hvLookup]
  have hveq : actualV = component := Option.some.inj (hv'.symm.trans hv)
  rw [hveq]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
    have := edges.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextIndex hnextIndex
  apply (WP.spec_ok _).mpr
  exact ⟨nextIndex, by simpa using hnextIndex, rfl⟩

end Labyrinth
