module
public import LabyrinthCore.Model
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
@[expose] public section

namespace Labyrinth

private theorem constructor_parentAt_mem (p : List Nat) (v : Nat) (hv : v < p.length) :
    parentAt p v ∈ p := by
  simp only [parentAt, List.getElem?_eq_getElem hv, Option.getD_some]
  exact List.getElem_mem hv

private theorem constructor_parentAt_lt {p : List Nat} {root : Nat}
    (h : RootedTree p root) {v : Nat} (hv : v < p.length) :
    parentAt p v < p.length :=
  h.2.2.1 _ (constructor_parentAt_mem p v hv)

private theorem constructor_follow_lt {p : List Nat} {root : Nat}
    (h : RootedTree p root) (k : Nat) {v : Nat} (hv : v < p.length) :
    follow p k v < p.length := by
  induction k generalizing v with
  | zero => exact hv
  | succ k ih => exact ih (constructor_parentAt_lt h hv)

private theorem constructor_follow_root {p : List Nat} {root : Nat}
    (h : RootedTree p root) (k : Nat) : follow p k root = root := by
  have hp : parentAt p root = root := by simp [parentAt, h.2.1]
  induction k with
  | zero => rfl
  | succ k ih => simpa [follow, hp] using ih

/-- Undirected graph carried by the shared parent-array representation. -/
def constructorParentGraph (p : List Nat) : SimpleGraph (Fin p.length) where
  Adj u v := u ≠ v ∧ (parentAt p u.val = v.val ∨ parentAt p v.val = u.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The graph interpretation has exactly the undirected edges of `Model.parentEdge`. -/
theorem constructor_parentGraph_adj_iff (p : List Nat) (u v : Fin p.length) :
    (constructorParentGraph p).Adj u v ↔ parentEdge p u.val v.val := by
  simp only [constructorParentGraph, parentEdge, parentAt,
    List.getElem?_eq_getElem u.isLt, List.getElem?_eq_getElem v.isLt,
    Option.getD_some, Option.some.injEq]
  constructor
  · rintro ⟨hne, hp⟩
    exact ⟨u.isLt, v.isLt, fun he => hne (Fin.ext he), hp⟩
  · rintro ⟨_, _, hne, hp⟩
    exact ⟨fun he => hne (congrArg Fin.val he), hp⟩

private def constructorParent {p : List Nat} {root : Nat} (h : RootedTree p root)
    (v : Fin p.length) : Fin p.length :=
  ⟨parentAt p v.val, constructor_parentAt_lt h v.isLt⟩

private theorem constructor_reachable_parent {p : List Nat} {root : Nat}
    (h : RootedTree p root) (v : Fin p.length) :
    (constructorParentGraph p).Reachable v (constructorParent h v) := by
  by_cases he : v = constructorParent h v
  · simpa only [← he] using
      (SimpleGraph.Reachable.refl (G := constructorParentGraph p) v)
  · exact SimpleGraph.Adj.reachable ⟨he, Or.inl rfl⟩

private theorem constructor_reachable_follow {p : List Nat} {root : Nat}
    (h : RootedTree p root) (k : Nat) (v : Fin p.length) :
    (constructorParentGraph p).Reachable v
      ⟨follow p k v.val, constructor_follow_lt h k v.isLt⟩ := by
  induction k generalizing v with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ k ih =>
    exact (constructor_reachable_parent h v).trans (ih (constructorParent h v))

/-- Reaching the designated root in the shared representation implies undirected connectivity. -/
theorem constructor_rooted_connected {p : List Nat} {root : Nat}
    (h : RootedTree p root) : (constructorParentGraph p).Connected := by
  let r : Fin p.length := ⟨root, h.1⟩
  have hr (v : Fin p.length) : (constructorParentGraph p).Reachable v r := by
    have hv := constructor_reachable_follow h p.length v
    simpa only [h.2.2.2 v.val v.isLt] using hv
  let : Nonempty (Fin p.length) := ⟨r⟩
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

private def constructorDescendant (p : List Nat) (a v : Nat) : Prop :=
  ∃ k, follow p k v = a

private theorem constructor_descendant_parent {p : List Nat} {a v : Nat}
    (h : constructorDescendant p a v) (hne : v ≠ a) :
    constructorDescendant p a (parentAt p v) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact (hne hk).elim
  | succ k => exact ⟨k, hk⟩

private theorem constructor_descendant_child {p : List Nat} {a v : Nat}
    (h : constructorDescendant p a (parentAt p v)) :
    constructorDescendant p a v := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, hk⟩

private theorem constructor_walk_closed {V : Type*} {G : SimpleGraph V}
    (P : V → Prop) (h : ∀ {u v}, G.Adj u v → P u → P v)
    {u v : V} (w : G.Walk u v) : P u → P v := by
  induction w with
  | nil => exact id
  | cons hadj w ih => exact fun hu => ih (h hadj hu)

private theorem constructor_parent_edge_forced {p : List Nat} {root : Nat}
    (h : RootedTree p root) (H : SimpleGraph (Fin p.length))
    (hle : H ≤ constructorParentGraph p) (hc : H.Connected)
    (a : Fin p.length) (ha : a.val ≠ root) : H.Adj a (constructorParent h a) := by
  classical
  by_contra hn
  let P : Fin p.length → Prop := fun v => constructorDescendant p a.val v.val
  have hclosed : ∀ {u v}, H.Adj u v → P u → P v := by
    intro u v huv hu
    obtain ⟨_, hp | hp⟩ := hle huv
    · by_cases hua : u = a
      · subst u
        have hv : v = constructorParent h a := Fin.ext hp.symm
        subst v
        exact (hn huv).elim
      · have hval : u.val ≠ a.val := fun he => hua (Fin.ext he)
        have hd := constructor_descendant_parent hu hval
        simpa only [hp] using hd
    · apply constructor_descendant_child
      simpa only [hp] using hu
  let r : Fin p.length := ⟨root, h.1⟩
  obtain ⟨w⟩ := hc a r
  have hr : P r := constructor_walk_closed P hclosed w ⟨0, rfl⟩
  obtain ⟨k, hk⟩ := hr
  exact ha ((constructor_follow_root h k).symm.trans hk).symm

/-- The shared rooted-parent predicate implies a genuine undirected, connected, acyclic tree. -/
theorem constructor_rooted_isTree {p : List Nat} {root : Nat}
    (h : RootedTree p root) : (constructorParentGraph p).IsTree := by
  apply SimpleGraph.isTree_of_minimal_connected
  refine ⟨constructor_rooted_connected h, ?_⟩
  intro H hc hle u v huv
  obtain ⟨hne, hp | hp⟩ := huv
  · have hu : u.val ≠ root := by
      intro he
      have hroot : parentAt p root = root := by simp [parentAt, h.2.1]
      have hv : u.val = v.val := by simpa only [he, hroot] using hp
      exact hne (Fin.ext hv)
    have hv : v = constructorParent h u := Fin.ext hp.symm
    subst v
    exact constructor_parent_edge_forced h H hle hc u hu
  · have hv : v.val ≠ root := by
      intro he
      have hroot : parentAt p root = root := by simp [parentAt, h.2.1]
      have hu : v.val = u.val := by simpa only [he, hroot] using hp
      exact hne (Fin.ext hu.symm)
    have hu : u = constructorParent h v := Fin.ext hp.symm
    subst u
    exact (constructor_parent_edge_forced h H hle hc v hv).symm

/-- `TreeValid` therefore denotes a tree, not merely a successful validation result. -/
theorem constructor_treeValid_isTree {c : labyrinth_core.topology.Carrier}
    {t : labyrinth_core.spanning_tree.Tree} (h : TreeValid c t) :
    (constructorParentGraph (parents t)).IsTree :=
  constructor_rooted_isTree h.2.1

end Labyrinth
