module
public import LabyrinthCore.ConstructorContraction
@[expose] public section

namespace Labyrinth

/-- Expanding a quotient step uses its retained original endpoints and the required paths inside
both endpoint classes. This preserves parallel-edge identities rather than inventing an edge. -/
theorem constructor_expansion_walk (n : Nat) (label : Nat → Nat)
    (quotient selected : Nat → Nat → Prop)
    (hclasses : ∀ u v, u < n → v < n → label u = label v →
      Relation.ReflTransGen selected u v)
    (hwitness : ∀ a b, quotient a b → ∃ u v,
      u < n ∧ v < n ∧ label u = a ∧ label v = b ∧ selected u v)
    {a b : Nat} (path : Relation.ReflTransGen quotient a b)
    (u v : Nat) (hu : u < n) (hv : v < n) (hul : label u = a) (hvl : label v = b) :
    Relation.ReflTransGen selected u v := by
  induction path generalizing v with
  | refl => exact hclasses u v hu hv (hul.trans hvl.symm)
  | @tail current next _ hedge ih =>
    obtain ⟨left, right, hl, hr, hll, hrl, hselected⟩ := hwitness current next hedge
    exact (ih left hl hll).trans
      ((Relation.ReflTransGen.single hselected).trans
        (hclasses right v hr hv (hrl.trans hvl.symm)))

/-- A connected quotient tree with original-edge witnesses expands to a connected global graph. -/
theorem constructor_expansion_connected (n : Nat) (label : Nat → Nat)
    (quotient selected : Nat → Nat → Prop)
    (hclasses : ∀ u v, u < n → v < n → label u = label v →
      Relation.ReflTransGen selected u v)
    (hwitness : ∀ a b, quotient a b → ∃ u v,
      u < n ∧ v < n ∧ label u = a ∧ label v = b ∧ selected u v)
    (hquotient : ∀ u v, u < n → v < n → Relation.ReflTransGen quotient (label u) (label v)) :
    ∀ u v, u < n → v < n → Relation.ReflTransGen selected u v := by
  intro u v hu hv
  exact constructor_expansion_walk n label quotient selected hclasses hwitness
    (hquotient u v hu hv) u v hu hv rfl rfl

/-- Inclusion of every required adjacency is sufficient to retain every required path during expansion. -/
theorem constructor_expansion_required_paths (required selected : Nat → Nat → Prop)
    (hinclude : ∀ u v, required u v → selected u v) {u v : Nat}
    (path : Relation.ReflTransGen required u v) : Relation.ReflTransGen selected u v := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge ih => exact ih.tail (hinclude _ _ edge)

end Labyrinth
