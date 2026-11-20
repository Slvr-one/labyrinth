module
public import LabyrinthCore.Types
public import LabyrinthCore.Funs

@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def offsets (c : topology.Carrier) : List Nat := c.offsets.val.map (·.val)
def neighbors (c : topology.Carrier) : List Nat := c.neighbors.val.map (·.val)
def cellCount (c : topology.Carrier) : Nat := c.offsets.val.length - 1

def row (c : topology.Carrier) (u : Nat) : List Nat :=
  let start := (offsets c)[u]?.getD 0
  let stop := (offsets c)[u + 1]?.getD 0
  ((neighbors c).drop start).take (stop - start)

def carrierEdge (c : topology.Carrier) (u v : Nat) : Prop :=
  u < cellCount c ∧ v ∈ row c u

def edgePairs (c : topology.Carrier) : List (Nat × Nat) :=
  c.edges.val.map (fun e => (e.u.val, e.v.val))

def CarrierValid (c : topology.Carrier) : Prop :=
  0 < cellCount c ∧
  (offsets c)[0]? = some 0 ∧
  (offsets c)[cellCount c]? = some (neighbors c).length ∧
  (∀ i, i < cellCount c →
    ((offsets c)[i]?.getD 0) ≤ ((offsets c)[i + 1]?.getD 0)) ∧
  (∀ u, u < cellCount c →
    (row c u).Nodup ∧ u ∉ row c u ∧
    ∀ v ∈ row c u, v < cellCount c ∧ u ∈ row c v) ∧
  (∀ u, u < cellCount c → Relation.ReflTransGen (carrierEdge c) 0 u) ∧
  (edgePairs c).Nodup ∧
  (∀ u v, (u, v) ∈ edgePairs c ↔ u < v ∧ carrierEdge c u v)

def parents (t : spanning_tree.Tree) : List Nat := t.parents.val.map (·.val)

def parentAt (p : List Nat) (v : Nat) : Nat := p[v]?.getD v

def follow (p : List Nat) : Nat → Nat → Nat
  | 0, v => v
  | k + 1, v => follow p k (parentAt p v)

def RootedTree (p : List Nat) (root : Nat) : Prop :=
  root < p.length ∧
  p[root]? = some root ∧
  (∀ v ∈ p, v < p.length) ∧
  (∀ v, v < p.length → follow p p.length v = root)

def parentEdge (p : List Nat) (u v : Nat) : Prop :=
  u < p.length ∧ v < p.length ∧ u ≠ v ∧
  (p[u]? = some v ∨ p[v]? = some u)

def TreeValid (c : topology.Carrier) (t : spanning_tree.Tree) : Prop :=
  (parents t).length = cellCount c ∧
  RootedTree (parents t) t.root.val ∧
  (∀ u, u < (parents t).length → u ≠ t.root.val →
    carrierEdge c u (parentAt (parents t) u))

def WorkspaceValid (w : spanning_tree.Workspace) : Prop :=
  let capacity := w.path.val.length
  w.seen.val.length = capacity ∧
  w.frames.val.length = capacity ∧
  w.parents.val.length = capacity ∧
  w.incoming.val.length = capacity ∧
  w.edit_slots.val.length = capacity ∧
  w.edit_nodes.val.length = capacity ∧
  w.edit_count.val ≤ capacity ∧
  ((w.edit_nodes.val.take w.edit_count.val).map (·.val)).Nodup ∧
  (∀ i, i < w.edit_count.val →
    ∃ node, w.edit_nodes.val[i]? = some node ∧ node.val < capacity ∧
      ∃ slot, w.edit_slots.val[node.val]? = some slot ∧ slot.val = i) ∧
  (∀ node, node < capacity →
    ∃ slot, w.edit_slots.val[node]? = some slot ∧
      (slot.val = Usize.max ∨
        (slot.val < w.edit_count.val ∧
          ∃ value, w.edit_nodes.val[slot.val]? = some value ∧ value.val = node)))

end Labyrinth
