module
public import LabyrinthCore.ConstructorSceneUnion
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Ranked links and stable component labels force the label itself to be the unique fixed root. -/
theorem constructor_component_root_properties (links : Slice Usize)
    (rank : Usize → Nat) (component : Usize → Usize)
    (hrank : constructorRankedLinks links rank)
    (hlabel : constructorComponentLabels links component)
    (node : Usize) (hnode : node.val < links.val.length) :
    (component node).val < links.val.length ∧
      links.val[(component node).val]? = some (component node) := by
  have hall : ∀ k, ∀ current : Usize, rank current = k → current.val < links.val.length →
      (component current).val < links.val.length ∧
        links.val[(component current).val]? = some (component current) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro current hk hc
      let parent := links.val[current.val]
      have hp : links.val[current.val]? = some parent := List.getElem?_eq_getElem hc
      by_cases he : parent = current
      · have hfixed : links.val[current.val]? = some current := by simpa only [he] using hp
        have hroot := hlabel.2 current hc hfixed
        simpa only [hroot] using And.intro hc hfixed
      · obtain ⟨hbound, hdecrease⟩ := hrank current parent hc hp
        have hparent := ih (rank parent) (by simpa only [hk] using hdecrease he)
          parent rfl hbound
        simpa only [hlabel.1 current parent hc hp] using hparent
  exact hall (rank node) node rfl hnode

/-- Actual required-edge union preserves termination ranks and exactly the two merged classes. -/
theorem constructor_join_required_structural_spec (carrier : topology.Carrier)
    (links sizes : Slice Usize) (edge : topology.Edge) (rank : Usize → Nat)
    (component : Usize → Usize)
    (hc : CarrierValid carrier) (he : carrierEdge carrier edge.u.val edge.v.val)
    (hlen : links.val.length = cellCount carrier) (hslen : sizes.val.length = links.val.length)
    (hrank : constructorRankedLinks links rank)
    (hlabel : constructorComponentLabels links component)
    (hdistinct : component edge.u ≠ component edge.v)
    (hsum : ∀ u v : Usize, u.val < links.val.length → v.val < links.val.length → u ≠ v →
      links.val[u.val]? = some u → links.val[v.val]? = some v →
      ∀ du dv : Usize, sizes.val[u.val]? = some du → sizes.val[v.val]? = some dv →
        du.val + dv.val ≤ Usize.max) :
    WP.spec (spanning_tree.join_required carrier links sizes edge) (fun output =>
      output.1 = .Ok () ∧ ∃ winner loser : Usize,
        ((winner = component edge.u ∧ loser = component edge.v) ∨
          (winner = component edge.v ∧ loser = component edge.u)) ∧
        constructorRankedLinks output.2.1 (constructorMergedRank rank component winner loser) ∧
        constructorComponentLabels output.2.1 (constructorMergedComponent component winner loser)) := by
  have hu : edge.u.val < links.val.length := by rw [hlen]; exact he.1
  have hv : edge.v.val < links.val.length := by
    rw [hlen]
    exact ((hc.2.2.2.2.1 edge.u.val he.1).2.2 edge.v.val he.2).1
  have huroot := constructor_component_root_properties links rank component hrank hlabel edge.u hu
  have hvroot := constructor_component_root_properties links rank component hrank hlabel edge.v hv
  apply WP.spec_mono (constructor_join_required_accepts carrier links sizes edge rank component
    hc he hlen hslen hrank hlabel hdistinct hsum)
  intro output hout
  obtain ⟨hok, winner, loser, ws, ls, combined, hchoice, _, _, _, _, hlinked, _⟩ := hout
  have hroots : winner.val < links.val.length ∧ loser.val < links.val.length ∧
      links.val[winner.val]? = some winner ∧ links.val[loser.val]? = some loser ∧ winner ≠ loser := by
    rcases hchoice with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨huroot.1, hvroot.1, huroot.2, hvroot.2, hdistinct⟩
    · exact ⟨hvroot.1, huroot.1, hvroot.2, huroot.2, Ne.symm hdistinct⟩
  have hp := constructor_union_preserves links rank component winner loser hrank hlabel
    hroots.1 hroots.2.1 hroots.2.2.1 hroots.2.2.2.1 hroots.2.2.2.2
  exact ⟨hok, winner, loser, hchoice, by simpa only [hlinked] using hp.1,
    by simpa only [hlinked] using hp.2⟩

end Labyrinth
