module
public import LabyrinthCore.ConstructorUnion
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Adding a required undirected edge retains every earlier adjacency. -/
def constructorRequiredJoinArc (before : Usize → Usize → Prop)
    (source target u v : Usize) : Prop :=
  before u v ∨ (u = source ∧ v = target) ∨ (u = target ∧ v = source)

/-- The exact component equation for adding an undirected required edge.
This connects union labels to graph reachability, independently of the representative implementation. -/
theorem constructor_required_join_connected_iff
    (before : Usize → Usize → Prop) (component : Usize → Usize) (source target : Usize)
    (hcomponent : ∀ u v, Relation.ReflTransGen before u v ↔ component u = component v)
    (u v : Usize) :
    Relation.ReflTransGen (constructorRequiredJoinArc before source target) u v ↔
      component u = component v ∨
      (component u = component source ∧ component v = component target) ∨
      (component u = component target ∧ component v = component source) := by
  let merged : Usize → Usize := fun node =>
    if component node = component target then component source else component node
  have hmerged : ∀ x y,
      merged x = merged y ↔ component x = component y ∨
        (component x = component source ∧ component y = component target) ∨
        (component x = component target ∧ component y = component source) := by
    intro x y
    dsimp only [merged]
    by_cases hx : component x = component target <;>
      by_cases hy : component y = component target <;> simp_all [eq_comm]
  have hlift : ∀ {x y : Usize}, Relation.ReflTransGen before x y →
      Relation.ReflTransGen (constructorRequiredJoinArc before source target) x y := by
    intro x y path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ edge ih => exact ih.tail (Or.inl edge)
  constructor
  · intro path
    apply (hmerged u v).mp
    induction path with
    | refl => rfl
    | @tail current next _ edge ih =>
      apply ih.trans
      rcases edge with old | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have he := (hcomponent current next).mp (Relation.ReflTransGen.single old)
        simp only [merged, he]
      · rw [hx, hy]
        exact (hmerged source target).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · rw [hx, hy]
        exact (hmerged target source).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rintro (same | ⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact hlift ((hcomponent u v).mpr same)
    · exact (hlift ((hcomponent u source).mpr hu)).trans
        ((Relation.ReflTransGen.single (show constructorRequiredJoinArc before source target source target
          from Or.inr (Or.inl ⟨rfl, rfl⟩))).trans
          (hlift ((hcomponent target v).mpr hv.symm)))
    · exact (hlift ((hcomponent u target).mpr hu)).trans
        ((Relation.ReflTransGen.single (show constructorRequiredJoinArc before source target target source
          from Or.inr (Or.inr ⟨rfl, rfl⟩))).trans
          (hlift ((hcomponent source v).mpr hv.symm)))

end Labyrinth
