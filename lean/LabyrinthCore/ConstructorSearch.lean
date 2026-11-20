module
public import LabyrinthCore.ConstructorCarrierRows
public import Mathlib.Data.Finset.Card
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

def constructorCsrAdjacent (offsets neighbors : alloc.vec.Vec Usize) (u v : Nat) : Prop :=
  u < offsets.val.length - 1 ∧ ∃ j,
    (offsets.val[u]?.getD 0#usize).val ≤ j ∧
    j < (offsets.val[u + 1]?.getD 0#usize).val ∧
    ∃ value : Usize, neighbors.val[j]? = some value ∧ value.val = v

/-- A concrete work-stack invariant; the optional active vertex is the row currently being scanned. -/
structure constructorSearchState (n : Nat) (edge : Nat → Nat → Prop)
    (seen : alloc.vec.Vec Bool) (stack : alloc.vec.Vec Usize)
    (depth reached : Usize) (active : Option Nat) (visited : Finset Nat) : Prop where
  seen_length : seen.val.length = n
  stack_length : stack.val.length = n
  depth_le : depth.val ≤ reached.val
  reached_eq : reached.val = visited.card
  bounded : visited ⊆ Finset.range n
  root_mem : 0 ∈ visited
  seen_eq : ∀ v, v < n → seen.val[v]? = some (decide (v ∈ visited))
  pending : ∀ i, i < depth.val → ∃ cell : Usize,
    stack.val[i]? = some cell ∧ cell.val ∈ visited
  reachable : ∀ v ∈ visited, Relation.ReflTransGen edge 0 v
  covered : ∀ v ∈ visited,
    active = some v ∨ (∀ w, edge v w → w ∈ visited) ∨
      ∃ i, i < depth.val ∧ ∃ cell : Usize, stack.val[i]? = some cell ∧ cell.val = v

theorem constructor_search_card_bound {n : Nat} {edge : Nat → Nat → Prop}
    {seen : alloc.vec.Vec Bool} {stack : alloc.vec.Vec Usize}
    {depth reached : Usize} {active : Option Nat} {visited : Finset Nat}
    (h : constructorSearchState n edge seen stack depth reached active visited) :
    reached.val ≤ n := by
  have hc := Finset.card_le_card h.bounded
  simpa only [Finset.card_range, ← h.reached_eq] using hc

/-- Marking a previously unseen neighbor preserves the full concrete search invariant. -/
theorem constructor_search_push {n : Nat} {edge : Nat → Nat → Prop}
    {seen : alloc.vec.Vec Bool} {stack : alloc.vec.Vec Usize}
    {depth reached depth' reached' cell : Usize} {active : Option Nat} {visited : Finset Nat}
    (h : constructorSearchState n edge seen stack depth reached active visited)
    (hcell : cell.val < n) (hnew : cell.val ∉ visited)
    (hpath : Relation.ReflTransGen edge 0 cell.val)
    (hdepth : depth'.val = depth.val + 1) (hreached : reached'.val = reached.val + 1) :
    constructorSearchState n edge (seen.set cell true) (stack.set depth cell)
      depth' reached' active (insert cell.val visited) := by
  have hsubset : insert cell.val visited ⊆ Finset.range n := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_range.mpr hcell
    · exact h.bounded hv
  have hcard : (insert cell.val visited).card = visited.card + 1 :=
    Finset.card_insert_of_notMem hnew
  have hroom : depth.val < stack.val.length := by
    have hc := Finset.card_le_card hsubset
    rw [Finset.card_range, hcard] at hc
    have hd := h.depth_le
    have hr := h.reached_eq
    rw [h.stack_length]
    omega
  refine {
    seen_length := by simpa using h.seen_length
    stack_length := by simpa using h.stack_length
    depth_le := by have := h.depth_le; omega
    reached_eq := by rw [hcard, ← h.reached_eq]; exact hreached
    bounded := hsubset
    root_mem := Finset.mem_insert_of_mem h.root_mem
    seen_eq := ?_
    pending := ?_
    reachable := ?_
    covered := ?_
  }
  · intro v hv
    by_cases he : v = cell.val
    · subst v
      have hb : cell.val < seen.val.length := by rw [h.seen_length]; exact hcell
      simp [alloc.vec.Vec.set, hb]
    · simpa [alloc.vec.Vec.set, he, Ne.symm he] using h.seen_eq v hv
  · intro i hi
    by_cases he : i = depth.val
    · subst i
      exact ⟨cell, by simp [alloc.vec.Vec.set, hroom], Finset.mem_insert_self _ _⟩
    · obtain ⟨old, hold, hv⟩ := h.pending i (by omega)
      exact ⟨old, by simpa [alloc.vec.Vec.set, he, Ne.symm he] using hold,
        Finset.mem_insert_of_mem hv⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hpath
    · exact h.reachable v hv
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inr (Or.inr ⟨depth.val, by omega, cell,
        by simp [alloc.vec.Vec.set, hroom], rfl⟩)
    · rcases h.covered v hv with ha | hc | ⟨i, hi, old, hold, he⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl (fun w hw => Finset.mem_insert_of_mem (hc w hw)))
      · have hne : i ≠ depth.val := by omega
        exact Or.inr (Or.inr ⟨i, by omega, old,
          by simpa [alloc.vec.Vec.set, hne, Ne.symm hne] using hold, he⟩)

/-- Exhaustion makes the visited set exactly the root's reachable component, not merely a subset. -/
theorem constructor_search_exhausted {n : Nat} {edge : Nat → Nat → Prop}
    {seen : alloc.vec.Vec Bool} {stack : alloc.vec.Vec Usize}
    {depth reached : Usize} {visited : Finset Nat}
    (h : constructorSearchState n edge seen stack depth reached none visited)
    (hdepth : depth.val = 0) :
    (∀ v, v ∈ visited ↔ Relation.ReflTransGen edge 0 v) ∧
    (reached.val = n ↔ ∀ v, v < n → Relation.ReflTransGen edge 0 v) := by
  have hclosed : ∀ v ∈ visited, ∀ w, edge v w → w ∈ visited := by
    intro v hv
    rcases h.covered v hv with ha | hc | ⟨i, hi, _⟩
    · cases ha
    · exact hc
    · omega
  have hiff : ∀ v, v ∈ visited ↔ Relation.ReflTransGen edge 0 v := by
    intro v
    constructor
    · exact h.reachable v
    · intro hp
      induction hp with
      | refl => exact h.root_mem
      | tail _ edge ih => exact hclosed _ ih _ edge
  refine ⟨hiff, ?_⟩
  constructor
  · intro he v hv
    have hsets : visited = Finset.range n := by
      apply Finset.eq_of_subset_of_card_le h.bounded
      simp only [Finset.card_range, ← h.reached_eq, he, le_refl]
    exact (hiff v).mp (by rw [hsets]; exact Finset.mem_range.mpr hv)
  · intro hall
    have hsets : visited = Finset.range n := by
      apply Finset.Subset.antisymm h.bounded
      intro v hv
      exact (hiff v).mpr (hall v (Finset.mem_range.mp hv))
    rw [h.reached_eq, hsets, Finset.card_range]

/-- Finishing the active row restores the invariant used at the outer work-stack boundary. -/
theorem constructor_search_finish_row {n : Nat} {edge : Nat → Nat → Prop}
    {seen : alloc.vec.Vec Bool} {stack : alloc.vec.Vec Usize}
    {depth reached : Usize} {active : Nat} {visited : Finset Nat}
    (h : constructorSearchState n edge seen stack depth reached (some active) visited)
    (hclosed : ∀ w, edge active w → w ∈ visited) :
    constructorSearchState n edge seen stack depth reached none visited := by
  refine ⟨h.seen_length, h.stack_length, h.depth_le, h.reached_eq, h.bounded,
    h.root_mem, h.seen_eq, h.pending, h.reachable, ?_⟩
  intro v hv
  rcases h.covered v hv with ha | hc | hp
  · have he : active = v := Option.some.inj ha
    subst v
    exact Or.inr (Or.inl hclosed)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hp)

end Labyrinth
