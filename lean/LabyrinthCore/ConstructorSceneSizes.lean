module
public import LabyrinthCore.ConstructorSceneUnion
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Population is measured over the fixed vertex list, not over mutable size entries. -/
def constructorComponentPopulation (vertices : List Usize) (component : Usize → Usize)
    (root : Usize) : Nat :=
  (vertices.filter (fun node => component node == root)).length

/-- Distinct components have disjoint populations, giving the genuine arithmetic bound for union. -/
theorem constructor_component_population_pair_le (vertices : List Usize)
    (component : Usize → Usize) (u v : Usize) (hne : u ≠ v) :
    constructorComponentPopulation vertices component u +
      constructorComponentPopulation vertices component v ≤ vertices.length := by
  induction vertices with
  | nil => simp [constructorComponentPopulation]
  | cons node rest ih =>
    unfold constructorComponentPopulation at ih ⊢
    by_cases hu : component node = u <;> by_cases hv : component node = v <;>
      simp [hu, hv, hne, Ne.symm hne] at * <;> omega

/-- The winning population is exactly the sum, regardless of which size comparison won. -/
theorem constructor_component_population_merge_winner (vertices : List Usize)
    (component : Usize → Usize) (winner loser : Usize) (hne : winner ≠ loser) :
    constructorComponentPopulation vertices (constructorMergedComponent component winner loser) winner =
      constructorComponentPopulation vertices component winner +
        constructorComponentPopulation vertices component loser := by
  induction vertices with
  | nil => simp [constructorComponentPopulation]
  | cons node rest ih =>
    unfold constructorComponentPopulation at ih ⊢
    by_cases hw : component node = winner <;> by_cases hl : component node = loser <;>
      simp [constructorMergedComponent, hw, hl, hne, Ne.symm hne] at * <;> omega

/-- Every third component keeps exactly its old population. -/
theorem constructor_component_population_merge_other (vertices : List Usize)
    (component : Usize → Usize) (winner loser root : Usize)
    (hw : root ≠ winner) (hl : root ≠ loser) :
    constructorComponentPopulation vertices (constructorMergedComponent component winner loser) root =
      constructorComponentPopulation vertices component root := by
  unfold constructorComponentPopulation
  have hp : (fun node => constructorMergedComponent component winner loser node == root) =
      (fun node => component node == root) := by
    funext node
    by_cases hc : component node = loser
    · simp [constructorMergedComponent, hc, Ne.symm hw, Ne.symm hl]
    · simp [constructorMergedComponent, hc]
  rw [hp]

/-- Only fixed-point entries are semantically live in the generated size array. -/
def constructorComponentSizes (vertices : List Usize) (links sizes : Slice Usize)
    (component : Usize → Usize) : Prop :=
  ∀ root : Usize, root.val < links.val.length → links.val[root.val]? = some root →
    ∃ size : Usize, sizes.val[root.val]? = some size ∧
      size.val = constructorComponentPopulation vertices component root

/-- Root sizes bounded by a representable vertex universe discharge checked addition. -/
theorem constructor_component_sizes_sum (vertices : List Usize) (links sizes : Slice Usize)
    (component : Usize → Usize) (hsizes : constructorComponentSizes vertices links sizes component)
    (hwidth : vertices.length ≤ Usize.max) (u v : Usize)
    (hu : u.val < links.val.length) (hv : v.val < links.val.length) (hne : u ≠ v)
    (hur : links.val[u.val]? = some u) (hvr : links.val[v.val]? = some v)
    (du dv : Usize) (hdu : sizes.val[u.val]? = some du) (hdv : sizes.val[v.val]? = some dv) :
    du.val + dv.val ≤ Usize.max := by
  obtain ⟨su, hsu, huc⟩ := hsizes u hu hur
  obtain ⟨sv, hsv, hvc⟩ := hsizes v hv hvr
  have heu : du = su := Option.some.inj (hdu.symm.trans hsu)
  have hev : dv = sv := Option.some.inj (hdv.symm.trans hsv)
  subst du
  subst dv
  have := constructor_component_population_pair_le vertices component u v hne
  omega

/-- The actual two writes in union preserve exact populations at every surviving root. -/
theorem constructor_component_sizes_preserved (vertices : List Usize) (links sizes : Slice Usize)
    (component : Usize → Usize) (winner loser combined winnerSize loserSize : Usize)
    (hsize : constructorComponentSizes vertices links sizes component)
    (hslen : sizes.val.length = links.val.length)
    (hw : winner.val < links.val.length) (hl : loser.val < links.val.length)
    (hwr : links.val[winner.val]? = some winner) (hlr : links.val[loser.val]? = some loser)
    (hne : winner ≠ loser) (hws : sizes.val[winner.val]? = some winnerSize)
    (hls : sizes.val[loser.val]? = some loserSize)
    (hcombined : combined.val = winnerSize.val + loserSize.val) :
    constructorComponentSizes vertices (links.set loser winner) (sizes.set winner combined)
      (constructorMergedComponent component winner loser) := by
  obtain ⟨ws, hws', hwc⟩ := hsize winner hw hwr
  obtain ⟨ls, hls', hlc⟩ := hsize loser hl hlr
  have hew : winnerSize = ws := Option.some.inj (hws.symm.trans hws')
  have hel : loserSize = ls := Option.some.inj (hls.symm.trans hls')
  subst winnerSize
  subst loserSize
  intro root hr hfixed
  have hrb : root.val < links.val.length := by simpa [Slice.set] using hr
  have hrl : root ≠ loser := by
    intro he
    subst root
    have : some winner = some loser := by simpa [Slice.set, hl] using hfixed
    exact hne (Option.some.inj this)
  have hrlv : root.val ≠ loser.val := fun h => hrl ((UScalar.eq_equiv _ _).mpr h)
  have hfixed' : links.val[root.val]? = some root := by
    simpa [Slice.set, Slice.setAtNat, hrlv, Ne.symm hrlv] using hfixed
  by_cases hrw : root = winner
  · subst root
    refine ⟨combined, ?_, ?_⟩
    · simp [Slice.set, show winner.val < sizes.val.length by omega]
    · rw [constructor_component_population_merge_winner vertices component winner loser hne]
      omega
  · obtain ⟨size, hs, hc⟩ := hsize root hrb hfixed'
    refine ⟨size, ?_, ?_⟩
    · have hrwv : root.val ≠ winner.val := fun h => hrw ((UScalar.eq_equiv _ _).mpr h)
      simpa [Slice.set, Slice.setAtNat, hrwv, Ne.symm hrwv] using hs
    · rw [constructor_component_population_merge_other vertices component winner loser root hrw hrl]
      exact hc

end Labyrinth
