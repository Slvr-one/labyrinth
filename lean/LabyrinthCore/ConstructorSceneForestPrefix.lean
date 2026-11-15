module
public import LabyrinthCore.ConstructorSceneForest
public import LabyrinthCore.ConstructorSceneUnion
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Required adjacency retains the actual input edge and its input slot. -/
def constructorRequiredPrefixArc (required : Slice topology.Edge) (processed : Nat)
    (u v : Usize) : Prop :=
  ∃ slot, slot < processed ∧ ∃ edge, required.val[slot]? = some edge ∧
    ((u = edge.u ∧ v = edge.v) ∨ (u = edge.v ∧ v = edge.u))

/-- A forest edge is in the carrier and does not close a path in the earlier required prefix. -/
def ConstructorRequiredForest (carrier : topology.Carrier) (required : Slice topology.Edge) : Prop :=
  ∀ slot, slot < required.val.length → ∀ edge, required.val[slot]? = some edge →
    carrierEdge carrier edge.u.val edge.v.val ∧
      ¬ Relation.ReflTransGen (constructorRequiredPrefixArc required slot) edge.u edge.v

theorem constructor_required_prefix_zero_iff (required : Slice topology.Edge) (u v : Usize) :
    Relation.ReflTransGen (constructorRequiredPrefixArc required 0) u v ↔ u = v := by
  constructor
  · intro path
    induction path with
    | refl => rfl
    | tail _ edge _ =>
      obtain ⟨slot, hs, _⟩ := edge
      omega
  · intro he
    subst v
    exact Relation.ReflTransGen.refl

/-- Advancing the prefix adds precisely the actual edge in that slot, in both directions. -/
theorem constructor_required_prefix_step (required : Slice topology.Edge) (processed : Nat)
    (edge : topology.Edge) (he : required.val[processed]? = some edge) :
    constructorRequiredPrefixArc required (processed + 1) =
      constructorRequiredJoinArc (constructorRequiredPrefixArc required processed) edge.u edge.v := by
  funext u v
  apply propext
  constructor
  · rintro ⟨slot, hs, actual, ha, hor⟩
    by_cases hslot : slot = processed
    · have ha' : actual = edge := by
        rw [hslot] at ha
        exact Option.some.inj (ha.symm.trans he)
      rw [ha'] at hor
      rcases hor with forward | backward
      · exact Or.inr (Or.inl forward)
      · exact Or.inr (Or.inr backward)
    · exact Or.inl ⟨slot, by omega, actual, ha, hor⟩
  · rintro (old | forward | backward)
    · obtain ⟨slot, hs, actual, ha, hor⟩ := old
      exact ⟨slot, by omega, actual, ha, hor⟩
    · exact ⟨processed, by omega, edge, he, Or.inl forward⟩
    · exact ⟨processed, by omega, edge, he, Or.inr backward⟩

/-- The concrete union's merged labels are exactly the next required-prefix components. -/
theorem constructor_required_prefix_merge_iff (required : Slice topology.Edge) (processed : Nat)
    (edge : topology.Edge) (he : required.val[processed]? = some edge)
    (component : Usize → Usize) (winner loser : Usize)
    (hcomponent : ∀ u v, Relation.ReflTransGen (constructorRequiredPrefixArc required processed) u v ↔
      component u = component v)
    (hchoice : (winner = component edge.u ∧ loser = component edge.v) ∨
      (winner = component edge.v ∧ loser = component edge.u)) (u v : Usize) :
    Relation.ReflTransGen (constructorRequiredPrefixArc required (processed + 1)) u v ↔
      constructorMergedComponent component winner loser u =
        constructorMergedComponent component winner loser v := by
  rw [constructor_required_prefix_step required processed edge he]
  rw [constructor_required_join_connected_iff _ component edge.u edge.v hcomponent]
  rw [constructor_merged_component_eq_iff]
  rcases hchoice with ⟨hw, hl⟩ | ⟨hw, hl⟩
  · rw [hw, hl]
  · rw [hw, hl]
    tauto

end Labyrinth
