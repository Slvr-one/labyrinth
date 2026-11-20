module
public import LabyrinthCore.ConstructorExpandedGraph
public import LabyrinthCore.ConstructorSceneExpansion
public import LabyrinthCore.ConstructorSceneSelection
public import LabyrinthCore.ConstructorTreeInterpretation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core


namespace Labyrinth
/-- Undirected incidence is unchanged by the constructor's canonical endpoint order. -/
theorem constructor_canonical_edge_incidence (edge : topology.Edge) (u v : Nat) :
    ((u = (constructorCanonicalEdge edge).u.val ∧
        v = (constructorCanonicalEdge edge).v.val) ∨
      (u = (constructorCanonicalEdge edge).v.val ∧
        v = (constructorCanonicalEdge edge).u.val)) ↔
    ((u = edge.u.val ∧ v = edge.v.val) ∨
      (u = edge.v.val ∧ v = edge.u.val)) := by
  unfold constructorCanonicalEdge
  split
  · rfl
  · tauto

theorem constructor_carrier_edge_facts (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edge : topology.Edge)
    (he : carrierEdge carrier edge.u.val edge.v.val) :
    edge.u.val < cellCount carrier ∧ edge.v.val < cellCount carrier ∧ edge.u ≠ edge.v := by
  have hv := (hc.2.2.2.2.1 edge.u.val he.1).2.2 edge.v.val he.2
  refine ⟨he.1, hv.1, ?_⟩
  intro huv
  have hval := congrArg UScalar.val huv
  apply (hc.2.2.2.2.1 edge.u.val he.1).2.1
  simpa only [hval] using he.2

theorem constructor_canonical_edge_carrier (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edge : topology.Edge)
    (he : carrierEdge carrier edge.u.val edge.v.val) :
    carrierEdge carrier (constructorCanonicalEdge edge).u.val
      (constructorCanonicalEdge edge).v.val := by
  unfold constructorCanonicalEdge
  split
  · exact he
  · obtain ⟨hv, hvu⟩ := (hc.2.2.2.2.1 edge.u.val he.1).2.2 edge.v.val he.2
    exact ⟨hv, hvu⟩


/-- The undirected finite edge represented by one bounded input-list slot. -/
def constructorSelectedEdge (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (index : Fin edges.length) : Sym2 (Fin n) :=
  let edge := edges[index]
  have facts := hedges edge (List.getElem_mem index.isLt)
  s(⟨edge.u.val, facts.1⟩, ⟨edge.v.val, facts.2.1⟩)

/-- Simple graph supported by a bounded, loop-free edge list, before carrier construction. -/
def constructorSelectedGraph (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v) :
    SimpleGraph (Fin n) where
  Adj u v := ∃ edge ∈ edges,
    (u.val = edge.u.val ∧ v.val = edge.v.val) ∨
      (u.val = edge.v.val ∧ v.val = edge.u.val)
  symm := ⟨by
    rintro u v ⟨edge, hedge, forward | backward⟩
    · exact ⟨edge, hedge, Or.inr ⟨forward.2, forward.1⟩⟩
    · exact ⟨edge, hedge, Or.inl ⟨backward.2, backward.1⟩⟩⟩
  loopless := ⟨by
    rintro u ⟨edge, hedge, forward | backward⟩
    · have hne := (hedges edge hedge).2.2
      apply hne
      apply (UScalar.eq_equiv _ _).mpr
      exact forward.1.symm.trans forward.2
    · have hne := (hedges edge hedge).2.2
      apply hne
      apply (UScalar.eq_equiv _ _).mpr
      exact backward.2.symm.trans backward.1⟩

/-- Input simplicity makes the slot-to-undirected-edge map injective. -/
theorem constructor_selectedEdge_injective (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hsimple : constructorEdgesSimple edges) :
    Function.Injective (constructorSelectedEdge n edges hedges) := by
  intro left right heq
  let edge := edges[left]
  let other := edges[right]
  have hedge : edges[left.val]? = some edge := by
    exact List.getElem?_eq_getElem left.isLt
  have hother : edges[right.val]? = some other := by
    exact List.getElem?_eq_getElem right.isLt
  have hpairs :
      (⟨edge.u.val, (hedges edge (List.getElem_mem left.isLt)).1⟩ : Fin n) =
          ⟨other.u.val, (hedges other (List.getElem_mem right.isLt)).1⟩ ∧
        (⟨edge.v.val, (hedges edge (List.getElem_mem left.isLt)).2.1⟩ : Fin n) =
          ⟨other.v.val, (hedges other (List.getElem_mem right.isLt)).2.1⟩ ∨
      (⟨edge.u.val, (hedges edge (List.getElem_mem left.isLt)).1⟩ : Fin n) =
          ⟨other.v.val, (hedges other (List.getElem_mem right.isLt)).2.1⟩ ∧
        (⟨edge.v.val, (hedges edge (List.getElem_mem left.isLt)).2.1⟩ : Fin n) =
          ⟨other.u.val, (hedges other (List.getElem_mem right.isLt)).1⟩ := by
    apply Sym2.eq_iff.mp
    simpa only [constructorSelectedEdge, edge, other] using heq
  have hindex : left.val = right.val := by
    apply hsimple left.val right.val edge other edge.u.val edge.v hedge hother
      (Or.inl ⟨rfl, rfl⟩)
    rcases hpairs with same | swapped
    · exact Or.inl ⟨congrArg (fun x : Fin n => x.val) same.1,
        (UScalar.eq_equiv _ _).mpr (congrArg (fun x : Fin n => x.val) same.2)⟩
    · exact Or.inr ⟨congrArg (fun x : Fin n => x.val) swapped.1,
        (UScalar.eq_equiv _ _).mpr (congrArg (fun x : Fin n => x.val) swapped.2)⟩
  exact Fin.ext hindex

/-- The list-supported graph has exactly the undirected images of its input slots. -/
theorem constructor_selectedGraph_edgeFinset_eq (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges,
      edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    [Fintype (constructorSelectedGraph n edges hedges).edgeSet] :
    (constructorSelectedGraph n edges hedges).edgeFinset =
      Finset.univ.image (constructorSelectedEdge n edges hedges) := by
  classical
  ext candidate
  induction candidate using Sym2.inductionOn with
  | hf u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨edge, hedge, incidence⟩
        obtain ⟨index, hlookup⟩ := List.mem_iff_getElem?.mp hedge
        have hindex : index < edges.length := (List.getElem?_eq_some_iff.mp hlookup).1
        let actual : Fin edges.length := ⟨index, hindex⟩
        have heq : edges[actual] = edge := by
          apply Option.some.inj
          exact (List.getElem?_eq_getElem hindex).symm.trans hlookup
        apply Finset.mem_image.mpr
        refine ⟨actual, Finset.mem_univ actual, ?_⟩
        apply Sym2.eq_iff.mpr
        rcases incidence with forward | backward
        · left
          exact ⟨Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              forward.1.symm),
            Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              forward.2.symm)⟩
        · right
          exact ⟨Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              backward.2.symm),
            Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              backward.1.symm)⟩
      · intro himage
        obtain ⟨index, _, heq⟩ := Finset.mem_image.mp himage
        let edge := edges[index]
        have incidence := Sym2.eq_iff.mp heq
        refine ⟨edge, List.getElem_mem index.isLt, ?_⟩
        rcases incidence with forward | backward
        · exact Or.inl ⟨congrArg Fin.val forward.1 |>.symm,
            congrArg Fin.val forward.2 |>.symm⟩
        · exact Or.inr ⟨congrArg Fin.val backward.2 |>.symm,
            congrArg Fin.val backward.1 |>.symm⟩

/-- The relation-level connectivity used by scene expansion is connectivity of the finite
list-supported graph. -/
theorem constructor_selectedGraph_connected (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges,
      edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hn : 0 < n)
    (hconnected : ∀ v, v < n →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v) :
    (constructorSelectedGraph n edges hedges).Connected := by
  let zero : Fin n := ⟨0, hn⟩
  have reachesZero : ∀ {v : Nat},
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v →
      ∀ hv : v < n, (constructorSelectedGraph n edges hedges).Reachable zero ⟨v, hv⟩ := by
    intro v path
    induction path with
    | refl =>
        intro _
        exact SimpleGraph.Reachable.refl
          (G := constructorSelectedGraph n edges hedges) zero
    | @tail current next path step ih =>
        intro hnext
        obtain ⟨edge, hedge, incidence⟩ := step
        have facts := hedges edge hedge
        have hcurrent : current < n := by
          rcases incidence with forward | backward <;> omega
        exact (ih hcurrent).trans (SimpleGraph.Adj.reachable
          ⟨edge, hedge, incidence⟩)
  let : Nonempty (Fin n) := ⟨zero⟩
  refine ⟨fun u v => ?_⟩
  exact (reachesZero (hconnected u.val u.isLt) u.isLt).symm.trans
    (reachesZero (hconnected v.val v.isLt) v.isLt)

/-- Connectivity and the selected `n - 1` cardinality force absence of duplicate undirected
input edges; simplicity is derived rather than assumed from construction. -/
theorem constructor_edges_simple_of_connected_cardinality (n : Nat)
    (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges,
      edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hn : 0 < n)
    (hconnected : ∀ v, v < n →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v)
    (hlength : edges.length + 1 = n) :
    constructorEdgesSimple edges := by
  classical
  let graph := constructorSelectedGraph n edges hedges
  have := Fintype.ofFinite graph.edgeSet
  let edgeOf := constructorSelectedEdge n edges hedges
  have hgraph : graph.Connected :=
    constructor_selectedGraph_connected n edges hedges hn hconnected
  have hlower := hgraph.card_vert_le_card_edgeSet_add_one
  have hedgeFinset :
      graph.edgeFinset = Finset.univ.image edgeOf := by
    exact constructor_selectedGraph_edgeFinset_eq n edges hedges
  have hlower' : n ≤ (Finset.univ.image edgeOf).card + 1 := by
    simpa only [graph, edgeOf, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card, hedgeFinset, Fintype.card_fin] using hlower
  have hupper :
      (Finset.univ.image edgeOf).card ≤ edges.length := by
    exact (Finset.card_image_le.trans_eq (by simp))
  have hcard :
      (Finset.univ.image edgeOf).card = (Finset.univ : Finset (Fin edges.length)).card := by
    apply Nat.le_antisymm Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hinjective : Function.Injective edgeOf := by
    intro left right heq
    exact Finset.injOn_of_card_image_eq (s := Finset.univ) (f := edgeOf) hcard
      (Finset.mem_univ left) (Finset.mem_univ right) heq
  intro i j edge other cell value hedge hother hincidence hotherIncidence
  have hi : i < edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have hj : j < edges.length := (List.getElem?_eq_some_iff.mp hother).1
  let left : Fin edges.length := ⟨i, hi⟩
  let right : Fin edges.length := ⟨j, hj⟩
  have hleft : edges[left] = edge := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hi).symm.trans hedge
  have hright : edges[right] = other := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hj).symm.trans hother
  have hedgeEq : edgeOf left = edgeOf right := by
    apply Sym2.eq_iff.mpr
    rcases hincidence with forward | backward <;>
      rcases hotherIncidence with otherForward | otherBackward
    · left
      exact ⟨Fin.ext (by simpa only [edgeOf, constructorSelectedEdge, left, right,
          hleft, hright] using forward.1.symm.trans otherForward.1),
        Fin.ext (by
          have he := congrArg UScalar.val (forward.2.symm.trans otherForward.2)
          simpa only [edgeOf, constructorSelectedEdge, left, right, hleft, hright] using he)⟩
    · right
      exact ⟨Fin.ext (by simpa only [edgeOf, constructorSelectedEdge, left, right,
          hleft, hright] using forward.1.symm.trans otherBackward.1),
        Fin.ext (by
          have he := congrArg UScalar.val (forward.2.symm.trans otherBackward.2)
          simpa only [edgeOf, constructorSelectedEdge, left, right, hleft, hright] using he)⟩
    · right
      exact ⟨Fin.ext (by
          have he := congrArg UScalar.val (backward.2.symm.trans otherForward.2)
          simpa only [edgeOf, constructorSelectedEdge, left, right, hleft, hright] using he),
        Fin.ext (by simpa only [edgeOf, constructorSelectedEdge, left, right,
          hleft, hright] using backward.1.symm.trans otherForward.1)⟩
    · left
      exact ⟨Fin.ext (by
          have he := congrArg UScalar.val (backward.2.symm.trans otherBackward.2)
          simpa only [edgeOf, constructorSelectedEdge, left, right, hleft, hright] using he),
        Fin.ext (by simpa only [edgeOf, constructorSelectedEdge, left, right,
          hleft, hright] using backward.1.symm.trans otherBackward.1)⟩
  exact congrArg Fin.val (hinjective hedgeEq)


/-- Exact `from_edges` adjacency identifies the carrier edge finset with the injective image
of the selected input slots. -/
theorem constructor_carrierGraph_edgeFinset_eq (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges,
      edge.u.val < cellCount carrier ∧ edge.v.val < cellCount carrier ∧ edge.u ≠ edge.v)
    (hexact : ∀ u v, carrierEdge carrier u v ↔
      ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
        (u = edge.v.val ∧ v = edge.u.val))
    [Fintype (constructorCarrierGraph carrier).edgeSet] :
    (constructorCarrierGraph carrier).edgeFinset =
      Finset.univ.image (constructorSelectedEdge (cellCount carrier) edges hedges) := by
  classical
  ext candidate
  induction candidate using Sym2.inductionOn with
  | hf u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        constructor_carrierGraph_adj_iff carrier hc]
      constructor
      · intro hadj
        obtain ⟨edge, hedge, incidence⟩ := (hexact u.val v.val).mp hadj
        obtain ⟨index, hlookup⟩ := List.mem_iff_getElem?.mp hedge
        have hindex : index < edges.length := (List.getElem?_eq_some_iff.mp hlookup).1
        let actual : Fin edges.length := ⟨index, hindex⟩
        have heq : edges[actual] = edge := by
          apply Option.some.inj
          exact (List.getElem?_eq_getElem hindex).symm.trans hlookup
        apply Finset.mem_image.mpr
        refine ⟨actual, Finset.mem_univ actual, ?_⟩
        apply Sym2.eq_iff.mpr
        rcases incidence with forward | backward
        · left
          exact ⟨Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              forward.1.symm),
            Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              forward.2.symm)⟩
        · right
          exact ⟨Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              backward.2.symm),
            Fin.ext (by simpa only [constructorSelectedEdge, actual, heq] using
              backward.1.symm)⟩
      · intro himage
        obtain ⟨index, _, heq⟩ := Finset.mem_image.mp himage
        let edge := edges[index]
        have incidence := Sym2.eq_iff.mp heq
        apply (hexact u.val v.val).mpr
        refine ⟨edge, List.getElem_mem index.isLt, ?_⟩
        rcases incidence with forward | backward
        · exact Or.inl ⟨congrArg Fin.val forward.1 |>.symm,
            congrArg Fin.val forward.2 |>.symm⟩
        · exact Or.inr ⟨congrArg Fin.val backward.2 |>.symm,
            congrArg Fin.val backward.1 |>.symm⟩

/-- Carrier validation already supplies reachability from zero, hence graph connectivity. -/
theorem constructor_carrierGraph_connected (carrier : topology.Carrier)
    (hc : CarrierValid carrier) : (constructorCarrierGraph carrier).Connected := by
  let zero : Fin (cellCount carrier) := ⟨0, hc.1⟩
  have reachesZero : ∀ {v : Nat},
      Relation.ReflTransGen (carrierEdge carrier) 0 v →
      ∀ hv : v < cellCount carrier,
        (constructorCarrierGraph carrier).Reachable zero ⟨v, hv⟩ := by
    intro v path
    induction path with
    | refl =>
        intro _
        exact SimpleGraph.Reachable.refl (G := constructorCarrierGraph carrier) zero
    | @tail current next path edge ih =>
        intro hnext
        have hcurrent : current < cellCount carrier := edge.1
        exact (ih hcurrent).trans (SimpleGraph.Adj.reachable
          ((constructor_carrierGraph_adj_iff carrier hc ⟨current, hcurrent⟩
            ⟨next, hnext⟩).2 edge))
  let : Nonempty (Fin (cellCount carrier)) := ⟨zero⟩
  refine ⟨fun u v => ?_⟩
  exact (reachesZero (hc.2.2.2.2.2.1 u.val u.isLt) u.isLt).symm.trans
    (reachesZero (hc.2.2.2.2.2.1 v.val v.isLt) v.isLt)

/-- The actual selection classification derives bounded, nonloop carrier edges for every
selected slot from the required forest and retained quotient witnesses. -/
theorem constructor_scene_selected_edges_valid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (selected : alloc.vec.Vec topology.Edge)
    (componentCount quotientRoot : Usize) (chosen : Nat → topology.Edge)
    (hc : CarrierValid carrier) (hforest : ConstructorRequiredForest carrier required)
    (hselection : ∀ slot, slot < selected.val.length →
      (slot < required.val.length ∧
        selected.val[slot]? =
          (required.val[slot]?).map constructorCanonicalEdge) ∨
      ∃ node, node < componentCount.val ∧ node ≠ quotientRoot.val ∧
        slot = constructorSceneSelectedIndex required.val.length quotientRoot.val node ∧
        selected.val[slot]? = some (chosen node))
    (hchosen : ∀ node, node < componentCount.val → node ≠ quotientRoot.val →
      carrierEdge carrier (chosen node).u.val (chosen node).v.val) :
    ∀ edge ∈ selected.val,
      edge.u.val < cellCount carrier ∧ edge.v.val < cellCount carrier ∧ edge.u ≠ edge.v := by
  intro edge hedge
  obtain ⟨slot, hlookup⟩ := List.mem_iff_getElem?.mp hedge
  have hslot : slot < selected.val.length := (List.getElem?_eq_some_iff.mp hlookup).1
  rcases hselection slot hslot with requiredCase | chosenCase
  · obtain ⟨hrequired, hcopy⟩ := requiredCase
    cases horiginal : required.val[slot]? with
    | none =>
        simp only [horiginal, Option.map_none] at hcopy
        rw [hcopy] at hlookup
        contradiction
    | some original =>
        have heq : edge = constructorCanonicalEdge original :=
          Option.some.inj (hlookup.symm.trans (by
            simpa only [horiginal, Option.map_some] using hcopy))
        subst edge
        apply constructor_carrier_edge_facts carrier hc
        apply constructor_canonical_edge_carrier carrier hc original
        exact (hforest slot hrequired original horiginal).1
  · obtain ⟨node, hnode, hnonroot, _, hchosenLookup⟩ := chosenCase
    have heq : edge = chosen node :=
      Option.some.inj (hlookup.symm.trans hchosenLookup)
    subst edge
    exact constructor_carrier_edge_facts carrier hc (chosen node)
      (hchosen node hnode hnonroot)

/-- A connected exact edge-list carrier with one fewer simple edge than vertices is a tree. -/
theorem constructor_carrierGraph_isTree_of_exact (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges,
      edge.u.val < cellCount carrier ∧ edge.v.val < cellCount carrier ∧ edge.u ≠ edge.v)
    (hsimple : constructorEdgesSimple edges)
    (hexact : ∀ u v, carrierEdge carrier u v ↔
      ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
        (u = edge.v.val ∧ v = edge.u.val))
    (hlength : edges.length + 1 = cellCount carrier) :
    (constructorCarrierGraph carrier).IsTree := by
  classical
  have := Fintype.ofFinite (constructorCarrierGraph carrier).edgeSet
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨constructor_carrierGraph_connected carrier hc, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    constructor_carrierGraph_edgeFinset_eq carrier hc edges hedges hexact,
    Finset.card_image_of_injective _
      (constructor_selectedEdge_injective (cellCount carrier) edges hedges hsimple),
    Finset.card_univ, Fintype.card_fin]
  simpa using hlength

/-- Required-component paths plus the actual quotient parent tree connect the selected
original-edge graph. -/
theorem constructor_scene_selected_connected (n count : Nat) (p : List Nat) (root : Nat)
    (label : Nat → Nat) (selected : Nat → Nat → Prop)
    (hlength : p.length = count) (htree : RootedTree p root)
    (hlabel : ∀ u, u < n → label u < count)
    (hclasses : ∀ u v, u < n → v < n → label u = label v →
      Relation.ReflTransGen selected u v)
    (hwitness : ∀ a b, parentEdge p a b → ∃ u v,
      u < n ∧ v < n ∧ label u = a ∧ label v = b ∧ selected u v) :
    ∀ u v, u < n → v < n → Relation.ReflTransGen selected u v := by
  have hquotient : ∀ u v, u < n → v < n →
      Relation.ReflTransGen (parentEdge p) (label u) (label v) := by
    intro u v hu hv
    have hlu : label u < p.length := by rw [hlength]; exact hlabel u hu
    have hlv : label v < p.length := by rw [hlength]; exact hlabel v hv
    have reachable :
        (constructorParentGraph p).Reachable ⟨label u, hlu⟩ ⟨label v, hlv⟩ :=
      (constructor_rooted_connected htree) ⟨label u, hlu⟩ ⟨label v, hlv⟩
    have path := (SimpleGraph.reachable_iff_reflTransGen _ _).mp reachable
    exact path.lift Fin.val (fun a b edge =>
      (constructor_parentGraph_adj_iff p a b).mp edge)
  exact constructor_expansion_connected n label (parentEdge p) selected hclasses hwitness
    hquotient

/-- The actual `from_edges` call accepts a fully justified selected list and returns exactly
the valid expanded tree carrier consumed by orientation. -/
theorem constructor_scene_expanded_carrier_accepts (n : Usize)
    (selected : alloc.vec.Vec topology.Edge)
    (hn : n ≠ 0#usize)
    (hedges : ∀ edge ∈ selected.val,
      edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v)
    (hconnected : ∀ v, v < n.val →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v)
    (hlength : selected.val.length + 1 = n.val)
    (hwidth : constructorEdgesStorageFits n selected.slice) :
    WP.spec (topology.Carrier.from_edges n selected.slice) (fun result =>
      ∃ expanded, result = .Ok expanded ∧ CarrierValid expanded ∧
        n.val = cellCount expanded ∧
        (constructorCarrierGraph expanded).IsTree ∧
        ∀ u v, carrierEdge expanded u v ↔
          ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
            (u = edge.v.val ∧ v = edge.u.val)) := by
  have hnpos : 0 < n.val := by
    have hne : n.val ≠ 0 := fun h => hn ((UScalar.eq_equiv _ _).mpr h)
    omega
  have hsimple : constructorEdgesSimple selected.val :=
    constructor_edges_simple_of_connected_cardinality n.val selected.val hedges hnpos
      hconnected hlength
  apply WP.spec_mono
    (constructor_carrier_from_edges_accepts_exact n selected.slice hn hedges hsimple
      hconnected hwidth)
  rintro result ⟨expanded, hr, hc, hcount, hexact⟩
  have hedges' : ∀ edge ∈ selected.val,
      edge.u.val < cellCount expanded ∧ edge.v.val < cellCount expanded ∧ edge.u ≠ edge.v := by
    simpa only [hcount] using hedges
  have htree : (constructorCarrierGraph expanded).IsTree :=
    constructor_carrierGraph_isTree_of_exact expanded hc selected.val hedges' hsimple
      hexact (by omega)
  exact ⟨expanded, hr, hc, hcount.symm, htree, hexact⟩

/-- Exact selected adjacency plus the actual required-prefix copy proves required-edge
inclusion in the expanded carrier. -/
theorem constructor_scene_expanded_contains_required
    (required : Slice topology.Edge) (selected : alloc.vec.Vec topology.Edge)
    (expanded : topology.Carrier)
    (hprefix : ∀ slot, slot < required.val.length →
      selected.val[slot]? = (required.val[slot]?).map constructorCanonicalEdge)
    (hexact : ∀ u v, carrierEdge expanded u v ↔
      ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
        (u = edge.v.val ∧ v = edge.u.val)) :
    ∀ slot, slot < required.val.length → ∀ edge,
      required.val[slot]? = some edge →
      carrierEdge expanded edge.u.val edge.v.val := by
  intro slot hslot edge hedge
  have hselected :
      selected.val[slot]? = some (constructorCanonicalEdge edge) := by
    simpa only [hedge, Option.map_some] using hprefix slot hslot
  apply (hexact edge.u.val edge.v.val).mpr
  refine ⟨constructorCanonicalEdge edge, List.mem_of_getElem? hselected, ?_⟩
  exact (constructor_canonical_edge_incidence edge edge.u.val edge.v.val).mpr
    (Or.inl ⟨rfl, rfl⟩)

end Labyrinth
