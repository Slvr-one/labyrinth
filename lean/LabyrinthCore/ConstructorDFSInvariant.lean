module
public import LabyrinthCore.ConstructorDepthFirstModel
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Only the active prefix contributes fuel; stale popped frames are deliberately ignored. -/
def constructorDFSStackFuel : Nat → List spanning_tree.Frame → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | depth + 1, frame :: rest => frame.remaining.val + constructorDFSStackFuel depth rest

/-- One new frame can add at most one entire adjacency array, whereas one discovery consumes
an entire block of that size plus two. The remaining summands pay for scans and pops. -/
def constructorDFSMeasure (vertices slots reached depth : Nat)
    (frames : List spanning_tree.Frame) : Nat :=
  (vertices - reached) * (slots + 2) + constructorDFSStackFuel depth frames + depth

structure ConstructorDFSFrameValid (offsets : Slice Usize) (frame : spanning_tree.Frame) : Prop where
  cell : frame.cell.val < constructorDFSVertexCount offsets
  remaining : frame.remaining.val ≤ constructorDFSOffset offsets (frame.cell.val + 1) -
    constructorDFSOffset offsets frame.cell.val
  next : 0 < frame.remaining.val →
    constructorDFSOffset offsets frame.cell.val ≤ frame.next.val ∧
      frame.next.val < constructorDFSOffset offsets (frame.cell.val + 1)

/-- Ghost ranks are assigned only when the extracted discovery branch writes a previously
unseen vertex. The frontier records the original slots still owed by active cyclic scans. -/
structure ConstructorDFSInvariant (offsets neighbors : Slice Usize) (root capacity : Nat)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached depth : Nat)
    (visited : Finset Nat) (rank : Nat → Nat) : Prop where
  seen_length : seen.val.length = capacity
  frames_length : frames.val.length = capacity
  parents_length : parents.val.length = capacity
  incoming_length : incoming.val.length = capacity
  capacity_bound : constructorDFSVertexCount offsets ≤ capacity
  visited_bound : visited ⊆ Finset.range (constructorDFSVertexCount offsets)
  count : visited.card = reached
  seen_iff : ∀ v, v < constructorDFSVertexCount offsets →
    (seen.val[v]? = some true ↔ v ∈ visited)
  root_mem : root ∈ visited
  root_parent : ∃ value, parents.val[root]? = some value ∧ value.val = root
  depth_bound : depth ≤ reached
  parent : ∀ v ∈ visited, ∃ value, parents.val[v]? = some value ∧ value.val ∈ visited
  rank_bound : ∀ v ∈ visited, rank v < reached
  rank_decreases : ∀ v ∈ visited, v ≠ root →
    ∀ value, parents.val[v]? = some value → rank value.val < rank v
  witness : ∀ v ∈ visited, v ≠ root → constructorDFSIncoming offsets neighbors parents incoming v
  frame : ∀ i, i < depth → ∀ value, frames.val[i]? = some value →
    value.cell.val ∈ visited ∧ ConstructorDFSFrameValid offsets value
  frontier : ∀ u ∈ visited, ∀ slot value,
    constructorDFSOffset offsets u ≤ slot → slot < constructorDFSOffset offsets (u + 1) →
    neighbors.val[slot]? = some value → value.val ∉ visited →
    ∃ i frame, i < depth ∧ frames.val[i]? = some frame ∧
      frame.cell.val = u ∧ constructorDFSPending offsets frame slot

theorem constructor_dfs_reached_bound
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank) : reached ≤ constructorDFSVertexCount offsets := by
  have hc := Finset.card_le_card h.visited_bound
  simpa only [Finset.card_range, h.count] using hc

theorem constructor_dfs_unseen_reached_lt
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank) (v : Nat) (hv : v < constructorDFSVertexCount offsets)
    (hunseen : v ∉ visited) : reached < constructorDFSVertexCount offsets := by
  have hsubset : insert v visited ⊆ Finset.range (constructorDFSVertexCount offsets) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hm
    · subst x; exact Finset.mem_range.mpr hv
    · exact h.visited_bound hm
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hunseen, h.count, Finset.card_range] at hc
  omega

/-- At empty stack the frontier invariant is directed closure, not a validator-success premise. -/
theorem constructor_dfs_stack_empty_all_seen
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (hinput : ConstructorDFSInput offsets neighbors root)
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached 0 visited rank) :
    visited = Finset.range (constructorDFSVertexCount offsets) ∧
      reached = constructorDFSVertexCount offsets ∧
      ∀ v, v < constructorDFSVertexCount offsets → seen.val[v]? = some true := by
  have hall : ∀ v, v < constructorDFSVertexCount offsets → v ∈ visited := by
    apply constructor_dfs_exhaustion offsets neighbors root hinput (· ∈ visited) h.root_mem
    intro u v hu arc
    obtain ⟨_, slot, value, hlo, hhi, hlookup, rfl⟩ := arc
    by_contra hn
    obtain ⟨i, frame, hi, _⟩ := h.frontier u hu slot value hlo hhi hlookup hn
    omega
  have he : visited = Finset.range (constructorDFSVertexCount offsets) := by
    apply Finset.Subset.antisymm h.visited_bound
    intro v hv
    exact hall v (Finset.mem_range.mp hv)
  refine ⟨he, ?_, fun v hv => (h.seen_iff v hv).mpr (hall v hv)⟩
  rw [← h.count, he, Finset.card_range]

/-- The rank invariant proves the shared parent representation once reachability closes. -/
theorem constructor_dfs_invariant_rooted
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (hinput : ConstructorDFSInput offsets neighbors root)
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank)
    (hall : ∀ v, v < constructorDFSVertexCount offsets → v ∈ visited) :
    RootedTree ((parents.val.take (constructorDFSVertexCount offsets)).map (·.val)) root := by
  let p := (parents.val.take (constructorDFSVertexCount offsets)).map (·.val)
  have hlength : p.length = constructorDFSVertexCount offsets := by
    simp only [p, List.length_map, List.length_take, h.parents_length,
      Nat.min_eq_left h.capacity_bound]
  have hlookup (v : Nat) (hv : v < constructorDFSVertexCount offsets) :
      p[v]? = (parents.val[v]?).map (·.val) := by
    simp [p, hv]
  have hp (v : Nat) (hv : v < constructorDFSVertexCount offsets) :
      ∃ value, parents.val[v]? = some value ∧ value.val < constructorDFSVertexCount offsets := by
    obtain ⟨value, hl, hm⟩ := h.parent v (hall v hv)
    exact ⟨value, hl, Finset.mem_range.mp (h.visited_bound hm)⟩
  apply constructor_rooted_of_discovery_rank p root rank
  · simpa only [hlength] using hinput.root_lt
  · obtain ⟨value, hl, he⟩ := h.root_parent
    rw [hlookup root hinput.root_lt, hl]
    simp only [Option.map_some, he]
  · intro value hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hi' : i < constructorDFSVertexCount offsets := by simpa only [hlength] using hi
    obtain ⟨scalar, hs, hb⟩ := hp i hi'
    have hl := hlookup i hi'
    rw [List.getElem?_eq_getElem hi, hs] at hl
    have he' : p[i] = scalar.val := Option.some.inj hl
    rw [← he, he', hlength]
    exact hb
  · intro v hv
    have hv' : v < constructorDFSVertexCount offsets := by simpa only [hlength] using hv
    have hr := h.rank_bound v (hall v hv')
    have hn := constructor_dfs_reached_bound h
    omega
  · intro v hv hne
    have hv' : v < constructorDFSVertexCount offsets := by simpa only [hlength] using hv
    obtain ⟨value, hl, _⟩ := hp v hv'
    have hr := h.rank_decreases v (hall v hv') hne value hl
    simpa only [parentAt, hlookup v hv', hl, Option.map_some, Option.getD_some] using hr

/-- The extracted root writes establish the singleton discovery forest. -/
theorem constructor_dfs_invariant_initial
    (offsets neighbors : Slice Usize) (root : Usize) (capacity : Nat)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (frame : spanning_tree.Frame)
    (hinput : ConstructorDFSInput offsets neighbors root.val)
    (hseen : seen.val.length = capacity) (hframes : frames.val.length = capacity)
    (hparents : parents.val.length = capacity) (hincoming : incoming.val.length = capacity)
    (hcapacity : constructorDFSVertexCount offsets ≤ capacity)
    (hzero : ∀ v, v < constructorDFSVertexCount offsets → seen.val[v]? = some false)
    (hroot : parents.val[root.val]? = some root)
    (hcell : frame.cell = root) (hframe : ConstructorDFSFrameValid offsets frame)
    (hremaining : frame.remaining.val = constructorDFSOffset offsets (root.val + 1) -
      constructorDFSOffset offsets root.val) :
    ConstructorDFSInvariant offsets neighbors root.val capacity (seen.set root true)
      (frames.set 0#usize frame) parents incoming 1 1 {root.val} (fun _ => 0) := by
  have hr : root.val < capacity := by have := hinput.root_lt; omega
  have hc : 0 < capacity := by have := hinput.nonempty; omega
  refine {
    seen_length := ?_
    frames_length := ?_
    parents_length := hparents
    incoming_length := hincoming
    capacity_bound := hcapacity
    visited_bound := ?_
    count := by simp
    seen_iff := ?_
    root_mem := by simp
    root_parent := ⟨root, hroot, rfl⟩
    depth_bound := Nat.le_refl _
    parent := ?_
    rank_bound := ?_
    rank_decreases := ?_
    witness := ?_
    frame := ?_
    frontier := ?_ }
  · simpa [alloc.vec.Vec.set] using hseen
  · simpa [alloc.vec.Vec.set] using hframes
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    exact Finset.mem_range.mpr (he ▸ hinput.root_lt)
  · intro v hv
    by_cases he : v = root.val
    · subst v
      simp [alloc.vec.Vec.set, hseen, hr]
    · simp [alloc.vec.Vec.set, he, Ne.symm he, hzero v hv]
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    subst v
    exact ⟨root, hroot, by simp⟩
  · intro v _
    exact Nat.zero_lt_one
  · intro v hv hn
    exact False.elim (hn (Finset.mem_singleton.mp hv))
  · intro v hv hn
    exact False.elim (hn (Finset.mem_singleton.mp hv))
  · intro i hi value hl
    have hi0 : i = 0 := by omega
    subst i
    have he : value = frame := by
      have hx : (frames.set 0#usize frame).val[0]? = some frame := by
        simp [alloc.vec.Vec.set, hframes, hc]
      exact Option.some.inj (hl.symm.trans hx)
    subst value
    exact ⟨by simp [hcell], hframe⟩
  · intro u hu slot value hlo hhi _ _
    have he : u = root.val := Finset.mem_singleton.mp hu
    subst u
    have hrow : constructorDFSOffset offsets root.val <
        constructorDFSOffset offsets (root.val + 1) := by omega
    have hpos : 0 < frame.remaining.val := by omega
    refine ⟨0, frame, by omega, ?_, by simp only [hcell], ?_⟩
    · simp [alloc.vec.Vec.set, hframes, hc]
    · exact constructor_dfs_pending_full offsets frame (hframe.next hpos)
        (by simpa only [hcell] using hremaining) slot
        (by simpa only [hcell] using And.intro hlo hhi)

end Labyrinth
