module
public import LabyrinthCore.ConstructorContraction
public import LabyrinthCore.MutationValidate
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- A mathematical component label is constant along links and identifies each fixed point. -/
def constructorComponentLabels (links : Slice Usize) (component : Usize → Usize) : Prop :=
  (∀ node parent : Usize, node.val < links.val.length → links.val[node.val]? = some parent →
    component node = component parent) ∧
  (∀ node : Usize, node.val < links.val.length → links.val[node.val]? = some node →
    component node = node)

/-- The generated representative search returns the unique component root, not an arbitrary label. -/
theorem constructor_representative_component_spec (links : Slice Usize)
    (rank : Usize → Nat) (component : Usize → Usize)
    (hlinks : constructorRankedLinks links rank) (hlabels : constructorComponentLabels links component)
    (start : Usize) (hstart : start.val < links.val.length) :
    WP.spec (spanning_tree.representative links start) (fun result =>
      result = component start ∧ result.val < links.val.length ∧ links.val[result.val]? = some result) := by
  apply WP.spec_mono (constructor_representative_spec links rank hlinks start hstart)
  intro result hresult
  obtain ⟨hbound, hfixed, hpath⟩ := hresult
  have hpreserved : ∀ target : Usize,
      Relation.ReflTransGen (fun u v : Usize => links.val[u.val]? = some v) start target →
      target.val < links.val.length ∧ component start = component target := by
    intro target hp
    induction hp with
    | refl => exact ⟨hstart, rfl⟩
    | @tail current next _ hedge ih =>
      exact ⟨(hlinks current next ih.1 hedge).1, ih.2.trans (hlabels.1 current next ih.1 hedge)⟩
  have he := (hpreserved result hpath).2.trans (hlabels.2 result hbound hfixed)
  exact ⟨he.symm, hbound, hfixed⟩

/-- An acyclic required-edge join performs one union-by-size link update and one size addition.
The rank/label hypotheses describe the input forest; no hypothesis assumes the join succeeds. -/
theorem constructor_join_required_accepts (carrier : topology.Carrier)
    (links sizes : Slice Usize) (edge : topology.Edge) (rank : Usize → Nat)
    (component : Usize → Usize)
    (hcarrier : CarrierValid carrier) (hedge : carrierEdge carrier edge.u.val edge.v.val)
    (hlen : links.val.length = cellCount carrier) (hsizes : sizes.val.length = links.val.length)
    (hlinks : constructorRankedLinks links rank) (hlabels : constructorComponentLabels links component)
    (hdistinct : component edge.u ≠ component edge.v)
    (hsum : ∀ u v : Usize, u.val < links.val.length → v.val < links.val.length → u ≠ v →
      links.val[u.val]? = some u → links.val[v.val]? = some v →
      ∀ du dv : Usize, sizes.val[u.val]? = some du → sizes.val[v.val]? = some dv →
        du.val + dv.val ≤ Usize.max) :
    WP.spec (spanning_tree.join_required carrier links sizes edge) (fun result =>
      result.1 = .Ok () ∧ ∃ winner loser sizeWinner sizeLoser combined : Usize,
        ((winner = component edge.u ∧ loser = component edge.v) ∨
          (winner = component edge.v ∧ loser = component edge.u)) ∧
        sizes.val[winner.val]? = some sizeWinner ∧ sizes.val[loser.val]? = some sizeLoser ∧
        sizeLoser.val ≤ sizeWinner.val ∧ combined.val = sizeWinner.val + sizeLoser.val ∧
        result.2.1 = links.set loser winner ∧ result.2.2 = sizes.set winner combined) := by
  unfold spanning_tree.join_required
  apply WP.spec_bind (mutation_carrier_contains_total carrier edge hcarrier)
  intro contains hc
  have htrue : contains = true := hc.mpr hedge
  simp only [htrue, ite_true]
  apply WP.spec_bind (constructor_representative_component_spec links rank component hlinks hlabels
    edge.u (by rw [hlen]; exact hedge.1))
  intro u hu
  apply WP.spec_bind (constructor_representative_component_spec links rank component hlinks hlabels
    edge.v (by
      rw [hlen]
      exact ((hcarrier.2.2.2.2.1 edge.u.val hedge.1).2.2 edge.v.val hedge.2).1))
  intro v hv
  have huv : u ≠ v := by simpa only [hu.1, hv.1] using hdistinct
  simp only [huv, ite_false]
  apply WP.spec_bind (Slice.index_usize_spec sizes u (by
    change u.val < sizes.val.length
    rw [hsizes]
    exact hu.2.1))
  intro du hdu
  have hduLookup : sizes.val[u.val]? = some du := by
    rw [List.getElem?_eq_getElem (show u.val < sizes.val.length by rw [hsizes]; exact hu.2.1), hdu]
  apply WP.spec_bind (Slice.index_usize_spec sizes v (by
    change v.val < sizes.val.length
    rw [hsizes]
    exact hv.2.1))
  intro dv hdv
  have hdvLookup : sizes.val[v.val]? = some dv := by
    rw [List.getElem?_eq_getElem (show v.val < sizes.val.length by rw [hsizes]; exact hv.2.1), hdv]
  have hwidth := hsum u v hu.2.1 hv.2.1 huv hu.2.2 hv.2.2 du dv hduLookup hdvLookup
  have hswap : WP.spec (if du < dv then ok (core.mem.swap u v) else ok (u, v)) (fun pair =>
      ∃ winnerSize loserSize : Usize,
        ((pair.1 = u ∧ pair.2 = v) ∨ (pair.1 = v ∧ pair.2 = u)) ∧
        pair.1.val < links.val.length ∧ pair.2.val < links.val.length ∧
        sizes.val[pair.1.val]? = some winnerSize ∧ sizes.val[pair.2.val]? = some loserSize ∧
        loserSize.val ≤ winnerSize.val ∧ winnerSize.val + loserSize.val ≤ Usize.max) := by
    by_cases hlt : du < dv
    · simp only [hlt, ite_true, core.mem.swap]
      apply (WP.spec_ok _).mpr
      exact ⟨dv, du, Or.inr ⟨rfl, rfl⟩, hv.2.1, hu.2.1, hdvLookup, hduLookup,
        (by
          have h : du.val < dv.val := by simpa using hlt
          omega), (by omega)⟩
    · simp only [hlt, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨du, dv, Or.inl ⟨rfl, rfl⟩, hu.2.1, hv.2.1, hduLookup, hdvLookup,
        (by
          have h : ¬ du.val < dv.val := by simpa using hlt
          omega), hwidth⟩
  apply WP.spec_bind hswap
  rintro ⟨winner, loser⟩ ⟨winnerSize, loserSize, hchoice, hw, hl, hws, hls, horder, hwidth'⟩
  dsimp only at hchoice hw hl hws hls horder hwidth'
  apply WP.spec_bind (Slice.update_spec links loser winner hl)
  intro linked hlinked
  apply WP.spec_bind (Slice.index_usize_spec sizes loser (by
    change loser.val < sizes.val.length
    rw [hsizes]
    exact hl))
  intro actualLoser hal
  have halLookup : sizes.val[loser.val]? = some actualLoser := by
    rw [List.getElem?_eq_getElem (show loser.val < sizes.val.length by rw [hsizes]; exact hl), hal]
  have halEq : actualLoser = loserSize := Option.some.inj (halLookup.symm.trans hls)
  rw [halEq]
  apply WP.spec_bind (Slice.index_usize_spec sizes winner (by
    change winner.val < sizes.val.length
    rw [hsizes]
    exact hw))
  intro actualWinner haw
  have hawLookup : sizes.val[winner.val]? = some actualWinner := by
    rw [List.getElem?_eq_getElem (show winner.val < sizes.val.length by rw [hsizes]; exact hw), haw]
  have hawEq : actualWinner = winnerSize := Option.some.inj (hawLookup.symm.trans hws)
  rw [hawEq]
  apply WP.spec_bind (Usize.add_spec (x := winnerSize) (y := loserSize) hwidth')
  intro combined hcombined
  apply WP.spec_bind (Slice.update_spec sizes winner combined (by
    change winner.val < sizes.val.length
    rw [hsizes]
    exact hw))
  intro sized hsized
  apply (WP.spec_ok _).mpr
  exact ⟨rfl, winner, loser, winnerSize, loserSize, combined,
    by simpa only [hu.1, hv.1] using hchoice, hws, hls, horder, hcombined, hlinked, hsized⟩

end Labyrinth
