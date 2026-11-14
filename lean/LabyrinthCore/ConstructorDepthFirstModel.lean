module
public import LabyrinthCore.ConstructorCyclic
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def constructorDFSVertexCount (offsets : Slice Usize) : Nat := offsets.val.length - 1

def constructorDFSOffset (offsets : Slice Usize) (v : Nat) : Nat :=
  (offsets.val[v]?.map (·.val)).getD 0

/-- An arc retains the original adjacency slot; parallel slots are not identified. -/
def constructorDFSArc (offsets neighbors : Slice Usize) (u v : Nat) : Prop :=
  u < constructorDFSVertexCount offsets ∧
  ∃ k value, constructorDFSOffset offsets u ≤ k ∧
    k < constructorDFSOffset offsets (u + 1) ∧
    neighbors.val[k]? = some value ∧ value.val = v

/-- Raw directed CSR is sufficient for the shared DFS, including quotient multigraphs. -/
structure ConstructorDFSInput (offsets neighbors : Slice Usize) (root : Nat) : Prop where
  nonempty : 0 < constructorDFSVertexCount offsets
  root_lt : root < constructorDFSVertexCount offsets
  first : constructorDFSOffset offsets 0 = 0
  last : constructorDFSOffset offsets (constructorDFSVertexCount offsets) = neighbors.val.length
  ordered : ∀ v, v < constructorDFSVertexCount offsets →
    constructorDFSOffset offsets v ≤ constructorDFSOffset offsets (v + 1)
  bounded : ∀ value ∈ neighbors.val, value.val < constructorDFSVertexCount offsets
  reachable : ∀ v, v < constructorDFSVertexCount offsets →
    Relation.ReflTransGen (constructorDFSArc offsets neighbors) root v

def constructorDFSParents (offsets : Slice Usize) (work : spanning_tree.Workspace) : List Nat :=
  (work.parents.val.take (constructorDFSVertexCount offsets)).map (·.val)

/-- The selected edge is the exact slot written by the generated discovery branch. -/
def constructorDFSIncoming (offsets neighbors : Slice Usize)
    (parents incoming : alloc.vec.Vec Usize) (v : Nat) : Prop :=
  ∃ parent slot value,
    parents.val[v]? = some parent ∧ incoming.val[v]? = some slot ∧
    constructorDFSOffset offsets parent.val ≤ slot.val ∧
    slot.val < constructorDFSOffset offsets (parent.val + 1) ∧
    neighbors.val[slot.val]? = some value ∧ value.val = v

structure ConstructorDFSOutput (offsets neighbors : Slice Usize) (root : Usize)
    (before after : spanning_tree.Workspace) : Prop where
  valid : WorkspaceValid after
  path : after.path = before.path
  edge_capacity : after.edge_capacity = before.edge_capacity
  discovered : ∀ v, v < constructorDFSVertexCount offsets → after.seen.val[v]? = some true
  tree : RootedTree (constructorDFSParents offsets after) root.val
  incoming : ∀ v, v < constructorDFSVertexCount offsets → v ≠ root.val →
    constructorDFSIncoming offsets neighbors after.parents after.incoming v

/-- Monotonicity is derived, rather than demanded as a stronger raw-CSR premise. -/
theorem constructor_dfs_offset_mono (offsets neighbors : Slice Usize) (root : Nat)
    (h : ConstructorDFSInput offsets neighbors root) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ constructorDFSVertexCount offsets) :
    constructorDFSOffset offsets i ≤ constructorDFSOffset offsets j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (h.ordered j (by omega))

theorem constructor_dfs_offset_bound (offsets neighbors : Slice Usize) (root : Nat)
    (h : ConstructorDFSInput offsets neighbors root) (i : Nat)
    (hi : i ≤ constructorDFSVertexCount offsets) :
    constructorDFSOffset offsets i ≤ neighbors.val.length := by
  rw [← h.last]
  exact constructor_dfs_offset_mono offsets neighbors root h hi (Nat.le_refl _)

/-- Exhausting every pending row implies discovery of every root-reachable vertex. -/
theorem constructor_dfs_exhaustion (offsets neighbors : Slice Usize) (root : Nat)
    (h : ConstructorDFSInput offsets neighbors root) (seen : Nat → Prop)
    (hroot : seen root)
    (hclosed : ∀ u v, seen u → constructorDFSArc offsets neighbors u v → seen v) :
    ∀ v, v < constructorDFSVertexCount offsets → seen v := by
  intro v hv
  have hp := h.reachable v hv
  have hall : ∀ {v}, Relation.ReflTransGen (constructorDFSArc offsets neighbors) root v →
      seen v := by
    intro v path
    induction path with
    | refl => exact hroot
    | tail _ edge ih => exact hclosed _ _ ih edge
  exact hall hp

/-- Pending entries describe the actual next pointer and remaining count, not an alternative DFS. -/
def constructorDFSPending (offsets : Slice Usize) (frame : spanning_tree.Frame) (slot : Nat) : Prop :=
  ∃ step, step < frame.remaining.val ∧
    constructorCyclicIndex (constructorDFSOffset offsets frame.cell.val)
      (constructorDFSOffset offsets (frame.cell.val + 1)) frame.next.val step = slot

theorem constructor_dfs_pending_empty (offsets : Slice Usize) (frame : spanning_tree.Frame)
    (h : frame.remaining.val = 0) (slot : Nat) : ¬ constructorDFSPending offsets frame slot := by
  rintro ⟨step, hstep, _⟩
  omega

/-- Deleting the current slot from a cyclic scan leaves exactly its advanced suffix. -/
theorem constructor_dfs_pending_advance (offsets : Slice Usize)
    (frame advanced : spanning_tree.Frame) (slot : Nat)
    (hnext : constructorDFSOffset offsets frame.cell.val ≤ frame.next.val ∧
      frame.next.val < constructorDFSOffset offsets (frame.cell.val + 1))
    (hcell : advanced.cell = frame.cell)
    (hremaining : advanced.remaining.val = frame.remaining.val - 1)
    (hadvance : advanced.next.val = if frame.next.val + 1 =
      constructorDFSOffset offsets (frame.cell.val + 1)
      then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1)
    (hpending : constructorDFSPending offsets frame slot) (hne : slot ≠ frame.next.val) :
    constructorDFSPending offsets advanced slot := by
  obtain ⟨step, hstep, hindex⟩ := hpending
  have hpos : 0 < step := by
    by_contra hz
    have hs : step = 0 := by omega
    rw [hs, constructor_cyclic_index_zero _ _ _ hnext] at hindex
    exact hne hindex.symm
  refine ⟨step - 1, by omega, ?_⟩
  rw [hcell, hadvance]
  rw [← constructor_cyclic_index_step _ _ _ _ hnext]
  simpa only [Nat.sub_add_cancel hpos] using hindex

/-- A legal cyclic start includes every original slot, even parallel witnesses. -/
theorem constructor_dfs_pending_full (offsets : Slice Usize) (frame : spanning_tree.Frame)
    (hnext : constructorDFSOffset offsets frame.cell.val ≤ frame.next.val ∧
      frame.next.val < constructorDFSOffset offsets (frame.cell.val + 1))
    (hremaining : frame.remaining.val = constructorDFSOffset offsets (frame.cell.val + 1) -
      constructorDFSOffset offsets frame.cell.val) (slot : Nat)
    (hslot : constructorDFSOffset offsets frame.cell.val ≤ slot ∧
      slot < constructorDFSOffset offsets (frame.cell.val + 1)) :
    constructorDFSPending offsets frame slot := by
  obtain ⟨step, hs, hi⟩ := constructor_cyclic_index_covers _ _ _ slot hnext hslot
  exact ⟨step, by omega, hi⟩

end Labyrinth
