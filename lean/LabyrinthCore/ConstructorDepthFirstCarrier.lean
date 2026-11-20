module
public import LabyrinthCore.ConstructorDepthFirstModel
public import LabyrinthCore.ConstructorCarrierModel
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

theorem constructor_dfs_offset_value (values : Slice Usize) (index : Nat) :
    constructorDFSOffset values index = (values.val[index]?.getD 0#usize).val := by
  unfold constructorDFSOffset
  cases values.val[index]? <;> simp

theorem constructor_dfs_carrier_arc_iff (carrier : topology.Carrier) (u v : Nat) :
    constructorDFSArc (alloc.vec.Vec.deref carrier.offsets)
      (alloc.vec.Vec.deref carrier.neighbors) u v ↔ carrierEdge carrier u v := by
  rw [constructor_carrier_edge_iff]
  simp only [constructorDFSArc, constructorDFSVertexCount, constructor_dfs_offset_value,
    constructorCsrAdjacent, alloc.vec.Vec.deref, Slice.from_val]
  constructor
  · rintro ⟨hu, slot, value, hlo, hhi, hval, he⟩
    exact ⟨hu, slot, hlo, hhi, value, hval, he⟩
  · rintro ⟨hu, slot, hlo, hhi, value, hval, he⟩
    exact ⟨hu, slot, value, hlo, hhi, hval, he⟩

/-- Ordered CSR has no unowned original slots, including across empty rows. -/
theorem constructor_dfs_slot_covered (offset : Nat → Nat) (n slot : Nat)
    (hzero : offset 0 = 0) (hslot : slot < offset n) :
    ∃ u, u < n ∧ offset u ≤ slot ∧ slot < offset (u + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hbefore : slot < offset n
    · obtain ⟨u, hu, hlo, hhi⟩ := ih hbefore
      exact ⟨u, by omega, hlo, hhi⟩
    · exact ⟨n, by omega, by omega, hslot⟩

/-- Public validated carriers provide the raw directed contract at every bounded root. -/
theorem constructor_dfs_input_of_carrier (carrier : topology.Carrier) (root : Nat)
    (h : CarrierValid carrier) (hr : root < cellCount carrier) :
    ConstructorDFSInput (alloc.vec.Vec.deref carrier.offsets)
      (alloc.vec.Vec.deref carrier.neighbors) root := by
  let os := alloc.vec.Vec.deref carrier.offsets
  let ns := alloc.vec.Vec.deref carrier.neighbors
  have hcount : constructorDFSVertexCount os = cellCount carrier := by
    simp [os, constructorDFSVertexCount, cellCount, alloc.vec.Vec.deref]
  have hoff (v : Nat) : constructorDFSOffset os v = (offsets carrier)[v]?.getD 0 := by
    simp [os, constructorDFSOffset, offsets, alloc.vec.Vec.deref]
  have hfirst : constructorDFSOffset os 0 = 0 := by rw [hoff, h.2.1]; rfl
  have hlast : constructorDFSOffset os (cellCount carrier) = carrier.neighbors.val.length := by
    rw [hoff, h.2.2.1]
    simp only [Option.getD_some, neighbors, List.length_map]
  have hsym {u v : Nat} (he : carrierEdge carrier u v) : carrierEdge carrier v u := by
    obtain ⟨hv, hreverse⟩ := (h.2.2.2.2.1 u he.1).2.2 v he.2
    exact ⟨hv, hreverse⟩
  have hreverse {u v : Nat} (path : Relation.ReflTransGen (carrierEdge carrier) u v) :
      Relation.ReflTransGen (carrierEdge carrier) v u := by
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact (Relation.ReflTransGen.single (hsym edge)).trans ih
  change ConstructorDFSInput os ns root
  refine {
    nonempty := by simpa only [hcount] using h.1
    root_lt := by simpa only [hcount] using hr
    first := hfirst
    last := by simpa [ns, alloc.vec.Vec.deref, hcount] using hlast
    ordered := ?_
    bounded := ?_
    reachable := ?_ }
  · intro v hv
    simpa only [hoff] using h.2.2.2.1 v (by simpa only [hcount] using hv)
  · intro value hm
    obtain ⟨slot, hslot⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hslot
    obtain ⟨u, hu, hlo, hhi⟩ := constructor_dfs_slot_covered
      (constructorDFSOffset os) (cellCount carrier) slot hfirst (by
        rw [hlast]
        simpa [ns, alloc.vec.Vec.deref] using hb)
    have hedge : carrierEdge carrier u value.val :=
      (constructor_dfs_carrier_arc_iff carrier u value.val).mp
        ⟨by simpa [constructorDFSVertexCount, cellCount, alloc.vec.Vec.deref] using hu,
          slot, value, hlo, hhi, hslot, rfl⟩
    simpa only [hcount] using ((h.2.2.2.2.1 u hu).2.2 value.val hedge.2).1
  · intro v hv
    have hp := (hreverse (h.2.2.2.2.2.1 root hr)).trans
      (h.2.2.2.2.2.1 v (by simpa only [hcount] using hv))
    have hconvert {u v : Nat} (path : Relation.ReflTransGen (carrierEdge carrier) u v) :
        Relation.ReflTransGen
          (constructorDFSArc (alloc.vec.Vec.deref carrier.offsets)
            (alloc.vec.Vec.deref carrier.neighbors)) u v := by
      induction path with
      | refl => exact .refl
      | tail _ edge ih => exact ih.tail ((constructor_dfs_carrier_arc_iff carrier _ _).mpr edge)
    exact hconvert hp

/-- Copying the proved parent prefix publishes a valid tree, using carrier reciprocity only here. -/
theorem constructor_dfs_output_tree_valid (carrier : topology.Carrier) (root : Usize)
    (before after : spanning_tree.Workspace) (published : spanning_tree.Tree)
    (hc : CarrierValid carrier)
    (hcapacity : cellCount carrier ≤ before.path.val.length)
    (hout : ConstructorDFSOutput (alloc.vec.Vec.deref carrier.offsets)
      (alloc.vec.Vec.deref carrier.neighbors) root before after)
    (hcopy : published.parents.val = after.parents.val.take (cellCount carrier))
    (hroot : published.root = root) : TreeValid carrier published := by
  have hp : parents published =
      constructorDFSParents (alloc.vec.Vec.deref carrier.offsets) after := by
    simp only [parents, hcopy, constructorDFSParents, constructorDFSVertexCount,
      alloc.vec.Vec.deref, Slice.from_val, cellCount]
  have hlen : (parents published).length = cellCount carrier := by
    rw [hp]
    simp only [constructorDFSParents, List.length_map, List.length_take,
      constructorDFSVertexCount, alloc.vec.Vec.deref, Slice.from_val]
    apply Nat.min_eq_left
    rw [hout.valid.2.2.1, hout.path]
    exact hcapacity
  refine ⟨hlen, by simpa only [hp, hroot] using hout.tree, ?_⟩
  intro v hv hne
  have hvn : v < cellCount carrier := by simpa only [hlen] using hv
  obtain ⟨parent, slot, value, hpa, _hin, hlo, hhi, hval, he⟩ :=
    hout.incoming v (by
      simpa [constructorDFSVertexCount, cellCount, alloc.vec.Vec.deref] using hvn)
      (by simpa only [hroot] using hne)
  have hlookup : (parents published)[v]? = some parent.val := by
    simp [parents, hcopy, hvn, hpa]
  have hparent : parent.val < cellCount carrier := by
    have hb := hout.tree.2.2.1 parent.val
      (by rw [← hp]; exact List.mem_of_getElem? hlookup)
    simpa only [← hp, hlen] using hb
  have hedge : carrierEdge carrier parent.val v :=
    (constructor_dfs_carrier_arc_iff carrier parent.val v).mp
      ⟨by simpa [constructorDFSVertexCount, cellCount, alloc.vec.Vec.deref] using hparent,
        slot.val, value, hlo, hhi, hval, he⟩
  have hreverse := (hc.2.2.2.2.1 parent.val hparent).2.2 v hedge.2
  simpa only [carrierEdge, parentAt, hlookup, Option.getD_some] using And.intro hvn hreverse.2

end Labyrinth
