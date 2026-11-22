module
public import LabyrinthCore.ConstructorOrientationInitialize
public import LabyrinthCore.ConstructorDFS
public import LabyrinthCore.ConstructorExpandedGraph
public import Mathlib.Data.Finset.Card
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Concrete invariant of the extracted scene orientation stack. `active` is the row currently
being scanned by loop 9's inner loop. -/
structure ConstructorOrientationInvariant (carrier : topology.Carrier) (root capacity : Nat)
    (seen : alloc.vec.Vec Bool) (path parents : alloc.vec.Vec Usize) (depth : Nat)
    (active : Option Nat) (visited : Finset Nat) (rank : Nat → Nat) : Prop where
  seen_length : seen.val.length = capacity
  path_length : path.val.length = capacity
  parents_length : parents.val.length = cellCount carrier
  capacity_bound : cellCount carrier ≤ capacity
  visited_bound : visited ⊆ Finset.range (cellCount carrier)
  seen_iff : ∀ v, v < cellCount carrier → (seen.val[v]? = some true ↔ v ∈ visited)
  root_mem : root ∈ visited
  root_parent : ∃ value, parents.val[root]? = some value ∧ value.val = root
  depth_bound : depth ≤ visited.card
  pending : ∀ i, i < depth → ∃ cell : Usize,
    path.val[i]? = some cell ∧ cell.val ∈ visited
  parent : ∀ v ∈ visited, ∃ value, parents.val[v]? = some value ∧ value.val ∈ visited
  rank_bound : ∀ v ∈ visited, rank v < visited.card
  rank_decreases : ∀ v ∈ visited, v ≠ root → ∀ value,
    parents.val[v]? = some value → rank value.val < rank v
  parent_edge : ∀ v ∈ visited, v ≠ root → ∀ value,
    parents.val[v]? = some value → carrierEdge carrier value.val v
  covered : ∀ v ∈ visited,
    active = some v ∨ (∀ w, carrierEdge carrier v w → w ∈ visited) ∨
      ∃ i, i < depth ∧ ∃ cell : Usize, path.val[i]? = some cell ∧ cell.val = v

def constructorOrientationSeenCount (seen : alloc.vec.Vec Bool) (n : Nat) : Nat :=
  ((Finset.range n).filter fun v => seen.val[v]? = some true).card

theorem constructor_orientation_seen_count
    {carrier : topology.Carrier} {root capacity depth : Nat}
    {seen : alloc.vec.Vec Bool} {path parents : alloc.vec.Vec Usize} {active : Option Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorOrientationInvariant carrier root capacity seen path parents depth active
      visited rank) :
    constructorOrientationSeenCount seen (cellCount carrier) = visited.card := by
  apply congrArg Finset.card
  apply Finset.ext
  intro v
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hv, hs⟩
    exact (h.seen_iff v hv).mp hs
  · intro hv
    have hb := Finset.mem_range.mp (h.visited_bound hv)
    exact ⟨hb, (h.seen_iff v hb).mpr hv⟩

/-- Valid undirected carriers are reachable from every bounded requested root, not merely zero. -/
theorem constructor_orientation_reachable_from_root (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (root : Nat) (hroot : root < cellCount carrier) :
    ∀ v, v < cellCount carrier → Relation.ReflTransGen (carrierEdge carrier) root v := by
  have hsym {u v : Nat} (he : carrierEdge carrier u v) : carrierEdge carrier v u := by
    obtain ⟨hv, hreverse⟩ := (hc.2.2.2.2.1 u he.1).2.2 v he.2
    exact ⟨hv, hreverse⟩
  have hreverse {u v : Nat} (path : Relation.ReflTransGen (carrierEdge carrier) u v) :
      Relation.ReflTransGen (carrierEdge carrier) v u := by
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact (Relation.ReflTransGen.single (hsym edge)).trans ih
  intro v hv
  exact (hreverse (hc.2.2.2.2.2.1 root hroot)).trans (hc.2.2.2.2.2.1 v hv)

/-- Marking an unseen neighbor and recording its actual carrier parent preserves the invariant. -/
theorem constructor_orientation_push
    {carrier : topology.Carrier} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {path parents : alloc.vec.Vec Usize}
    {depth nextDepth : Usize} {active : Option Nat}
    {visited : Finset Nat} {rank : Nat → Nat} {cell neighbor : Usize}
    (h : ConstructorOrientationInvariant carrier root capacity seen path parents depth.val active
      visited rank)
    (hc : CarrierValid carrier)
    (hsource : cell.val ∈ visited)
    (hedge : carrierEdge carrier cell.val neighbor.val) (hnew : neighbor.val ∉ visited)
    (hseen : neighbor.val < seen.val.length) (hpath : depth.val < path.val.length)
    (hparents : neighbor.val < parents.val.length)
    (hnextDepth : nextDepth.val = depth.val + 1) :
    ConstructorOrientationInvariant carrier root capacity (seen.set neighbor true)
      (path.set depth neighbor) (parents.set neighbor cell) nextDepth.val active
      (insert neighbor.val visited)
      (fun v => if v = neighbor.val then visited.card else rank v) := by
  have hsourceBound : cell.val < cellCount carrier :=
    Finset.mem_range.mp (h.visited_bound hsource)
  have htarget : neighbor.val < cellCount carrier :=
    ((hc.2.2.2.2.1 cell.val hsourceBound).2.2 neighbor.val hedge.2).1
  have hsubset : insert neighbor.val visited ⊆ Finset.range (cellCount carrier) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_range.mpr htarget
    · exact h.visited_bound hv
  have hcard : (insert neighbor.val visited).card = visited.card + 1 :=
    Finset.card_insert_of_notMem hnew
  refine {
    seen_length := by simpa [alloc.vec.Vec.set] using h.seen_length
    path_length := by simpa [alloc.vec.Vec.set] using h.path_length
    parents_length := by simpa [alloc.vec.Vec.set] using h.parents_length
    capacity_bound := h.capacity_bound
    visited_bound := hsubset
    seen_iff := ?_
    root_mem := Finset.mem_insert_of_mem h.root_mem
    root_parent := ?_
    depth_bound := by rw [hcard, hnextDepth]; have := h.depth_bound; omega
    pending := ?_
    parent := ?_
    rank_bound := ?_
    rank_decreases := ?_
    parent_edge := ?_
    covered := ?_ }
  · intro v hv
    by_cases he : v = neighbor.val
    · subst v
      simp [alloc.vec.Vec.set, hseen]
    · simpa [alloc.vec.Vec.set, he, Ne.symm he] using h.seen_iff v hv
  · obtain ⟨value, hl, he⟩ := h.root_parent
    have hr : root ≠ neighbor.val := fun eq => hnew (eq ▸ h.root_mem)
    exact ⟨value, by simpa [alloc.vec.Vec.set, hr, Ne.symm hr] using hl, he⟩
  · intro i hi
    by_cases he : i = depth.val
    · subst i
      exact ⟨neighbor, by simp [alloc.vec.Vec.set, hpath], Finset.mem_insert_self _ _⟩
    · obtain ⟨old, hold, hm⟩ := h.pending i (by omega)
      exact ⟨old, by simpa [alloc.vec.Vec.set, he, Ne.symm he] using hold,
        Finset.mem_insert_of_mem hm⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨cell, by simp [alloc.vec.Vec.set, hparents], Finset.mem_insert_of_mem hsource⟩
    · obtain ⟨value, hl, hm⟩ := h.parent v hv
      have hnv : v ≠ neighbor.val := fun eq => hnew (eq ▸ hv)
      exact ⟨value, by simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hl,
        Finset.mem_insert_of_mem hm⟩
  · intro v hv
    rw [hcard]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · by_cases he : v = neighbor.val
      · exact False.elim (hnew (he ▸ hv))
      · simp only [he, ite_false]
        have := h.rank_bound v hv
        omega
  · intro v hv hroot value hl
    rcases Finset.mem_insert.mp hv with he | hv
    · subst v
      have heq : value = cell := by
        have hs : (parents.set neighbor cell).val[neighbor.val]? = some cell := by
          simp [alloc.vec.Vec.set, hparents]
        exact Option.some.inj (hl.symm.trans hs)
      subst value
      have hcellne : cell.val ≠ neighbor.val := fun eq => hnew (eq ▸ hsource)
      simpa only [ite_true, hcellne, ite_false] using h.rank_bound cell.val hsource
    · have hnv : v ≠ neighbor.val := fun eq => hnew (eq ▸ hv)
      have hold : parents.val[v]? = some value := by
        simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hl
      have hp := h.parent v hv
      obtain ⟨parent, hparent, hm⟩ := hp
      have heq : parent = value := Option.some.inj (hparent.symm.trans hold)
      subst parent
      have hvn : value.val ≠ neighbor.val := fun eq => hnew (eq ▸ hm)
      simpa only [hnv, hvn, ite_false] using h.rank_decreases v hv hroot value hold
  · intro v hv hroot value hl
    rcases Finset.mem_insert.mp hv with he | hv
    · subst v
      have heq : value = cell := by
        have hs : (parents.set neighbor cell).val[neighbor.val]? = some cell := by
          simp [alloc.vec.Vec.set, hparents]
        exact Option.some.inj (hl.symm.trans hs)
      simpa only [heq] using hedge
    · have hnv : v ≠ neighbor.val := fun eq => hnew (eq ▸ hv)
      have hold : parents.val[v]? = some value := by
        simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hl
      exact h.parent_edge v hv hroot value hold
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inr (Or.inr ⟨depth.val, by rw [hnextDepth]; omega, neighbor,
        by simp [alloc.vec.Vec.set, hpath], rfl⟩)
    · rcases h.covered v hv with ha | hc | ⟨i, hi, old, hold, he⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl (fun w hw => Finset.mem_insert_of_mem (hc w hw)))
      · have hne : i ≠ depth.val := by omega
        exact Or.inr (Or.inr ⟨i, by omega, old,
          by simpa [alloc.vec.Vec.set, hne, Ne.symm hne] using hold, he⟩)

/-- Closing the active row records the exact carrier-neighbor closure used by the outer loop. -/
theorem constructor_orientation_finish_row
    {carrier : topology.Carrier} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {path parents : alloc.vec.Vec Usize} {depth active : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorOrientationInvariant carrier root capacity seen path parents depth
      (some active) visited rank)
    (hclosed : ∀ w, carrierEdge carrier active w → w ∈ visited) :
    ConstructorOrientationInvariant carrier root capacity seen path parents depth none visited rank := by
  refine ⟨h.seen_length, h.path_length, h.parents_length, h.capacity_bound, h.visited_bound,
    h.seen_iff, h.root_mem, h.root_parent, h.depth_bound, h.pending, h.parent,
    h.rank_bound, h.rank_decreases, h.parent_edge, ?_⟩
  intro v hv
  rcases h.covered v hv with ha | hc | hp
  · have he : active = v := Option.some.inj ha
    subst v
    exact Or.inr (Or.inl hclosed)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hp)

/-- Empty stack plus the actual carrier connectivity means every carrier cell was reached. -/
theorem constructor_orientation_exhausted
    {carrier : topology.Carrier} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {path parents : alloc.vec.Vec Usize}
    {visited : Finset Nat} {rank : Nat → Nat}
    (hc : CarrierValid carrier) (hroot : root < cellCount carrier)
    (h : ConstructorOrientationInvariant carrier root capacity seen path parents 0 none visited rank) :
    visited = Finset.range (cellCount carrier) ∧
      ∀ v, v < cellCount carrier → seen.val[v]? = some true := by
  have hclosed : ∀ v ∈ visited, ∀ w, carrierEdge carrier v w → w ∈ visited := by
    intro v hv
    rcases h.covered v hv with ha | hc | ⟨i, hi, _⟩
    · cases ha
    · exact hc
    · omega
  have hall : ∀ v, v < cellCount carrier → v ∈ visited := by
    intro v hv
    have hp := constructor_orientation_reachable_from_root carrier hc root hroot v hv
    induction hp with
    | refl => exact h.root_mem
    | tail _ edge ih => exact hclosed _ (ih edge.1) _ edge
  have he : visited = Finset.range (cellCount carrier) := by
    apply Finset.Subset.antisymm h.visited_bound
    intro v hv
    exact hall v (Finset.mem_range.mp hv)
  exact ⟨he, fun v hv => (h.seen_iff v hv).mpr (hall v hv)⟩

/-- The concrete parent writes and discovery ranks publish the shared rooted-parent format. -/
theorem constructor_orientation_rooted
    {carrier : topology.Carrier} {root capacity depth : Nat}
    {seen : alloc.vec.Vec Bool} {path parents : alloc.vec.Vec Usize} {active : Option Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorOrientationInvariant carrier root capacity seen path parents depth active
      visited rank)
    (hall : ∀ v, v < cellCount carrier → v ∈ visited) :
    RootedTree (parents.val.map (·.val)) root := by
  let p := parents.val.map (·.val)
  have hlength : p.length = cellCount carrier := by simp [p, h.parents_length]
  have hlookup (v : Nat) (hv : v < cellCount carrier) :
      p[v]? = (parents.val[v]?).map (·.val) := by simp [p, hv, h.parents_length]
  apply constructor_rooted_of_discovery_rank p root rank
  · have hm := h.root_mem
    exact by simpa only [hlength] using Finset.mem_range.mp (h.visited_bound hm)
  · obtain ⟨value, hl, he⟩ := h.root_parent
    have hr : root < cellCount carrier := Finset.mem_range.mp (h.visited_bound h.root_mem)
    rw [hlookup root hr, hl]
    simp only [Option.map_some, he]
  · intro value hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hi' : i < cellCount carrier := by simpa only [hlength] using hi
    obtain ⟨scalar, hs, hb⟩ := h.parent i (hall i hi')
    have hl := hlookup i hi'
    rw [List.getElem?_eq_getElem hi, hs] at hl
    have he' : p[i] = scalar.val := Option.some.inj hl
    rw [← he, he', hlength]
    exact Finset.mem_range.mp (h.visited_bound hb)
  · intro v hv
    have hv' : v < cellCount carrier := by simpa only [hlength] using hv
    have hr := h.rank_bound v (hall v hv')
    have hc := Finset.card_le_card h.visited_bound
    simp only [Finset.card_range] at hc
    omega
  · intro v hv hne
    have hv' : v < cellCount carrier := by simpa only [hlength] using hv
    obtain ⟨value, hl, _⟩ := h.parent v (hall v hv')
    have hr := h.rank_decreases v (hall v hv') hne value hl
    simpa only [parentAt, hlookup v hv', hl, Option.map_some, Option.getD_some] using hr

end Labyrinth
