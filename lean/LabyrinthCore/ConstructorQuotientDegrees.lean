module
public import LabyrinthCore.ConstructorDegree
public import LabyrinthCore.ConstructorSceneInitialize
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Every crossing original edge contributes once to each quotient endpoint, including parallel edges. -/
def constructorQuotientDegreeSlot (edges : List topology.Edge) (label : Usize → Usize)
    (slot : Nat) : Nat → Nat
  | 0 => 0
  | processed + 1 =>
    let previous := constructorQuotientDegreeSlot edges label slot processed
    match edges[processed]? with
    | none => previous
    | some edge =>
      if label edge.u = label edge.v then previous else
        let quotient := constructorCanonicalEdge { u := label edge.u, v := label edge.v }
        if slot = quotient.u.val + 1 ∨ slot = quotient.v.val + 1 then previous + 1 else previous

theorem constructor_quotient_degree_le (edges : List topology.Edge) (label : Usize → Usize)
    (slot processed : Nat) : constructorQuotientDegreeSlot edges label slot processed ≤ processed := by
  induction processed with
  | zero => exact le_rfl
  | succ processed ih =>
    simp only [constructorQuotientDegreeSlot]
    split
    · omega
    · split
      · omega
      · split <;> omega

/-- Actual scene loop3 counts the exact quotient incidences and accepts parallel witnesses. -/
theorem constructor_quotient_degrees_spec (components : alloc.vec.Vec Usize)
    (componentCount : Usize) (edges : Slice topology.Edge) (counts : alloc.vec.Vec Usize)
    (label : Usize → Usize)
    (hcapacity : counts.val.length = componentCount.val + 1)
    (hzero : ∀ j, j < counts.val.length → counts.val[j]? = some 0#usize)
    (hlabels : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? = some (label node))
    (hedges : ∀ edge ∈ edges.val,
      edge.u.val < components.val.length ∧ edge.v.val < components.val.length ∧
      (label edge.u).val < componentCount.val ∧ (label edge.v).val < componentCount.val) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop3 0#usize (.Ok ()) components componentCount counts edges)
      (fun output => output.1 = .Ok () ∧ output.2.val.length = counts.val.length ∧
        ∀ j, j < counts.val.length → ∃ value : Usize, output.2.val[j]? = some value ∧
          value.val = constructorQuotientDegreeSlot edges.val label j edges.val.length) := by
  let invariant : Usize × core.result.Result Unit topology.Error × alloc.vec.Vec Usize → Prop :=
    fun state => state.1.val ≤ edges.val.length ∧ state.2.1 = .Ok () ∧
      state.2.2.val.length = counts.val.length ∧
      ∀ j, j < counts.val.length → ∃ value : Usize, state.2.2.val[j]? = some value ∧
        value.val = constructorQuotientDegreeSlot edges.val label j state.1.val
  unfold spanning_tree.Tree.scene_dfs_loop3
  apply loop.spec_decr_nat
    (fun state : Usize × core.result.Result Unit topology.Error × alloc.vec.Vec Usize =>
      edges.val.length - state.1.val) invariant
  · rintro ⟨index, status, current⟩ hi
    obtain ⟨hindex, hstatus, hlen, hcounts⟩ := hi
    dsimp only at hindex hstatus hlen hcounts
    unfold spanning_tree.Tree.scene_dfs_loop3.body
    by_cases hmore : index < Slice.len edges
    · have hib : index.val < edges.val.length := by simpa using hmore
      simp only [hmore, ite_true, hstatus, core.result.Result.is_ok, bind_ok,
        alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (Slice.index_usize_spec edges index hib)
      intro edge he
      have heLookup : edges.val[index.val]? = some edge := by
        rw [List.getElem?_eq_getElem hib, he]
      have heMem : edge ∈ edges.val := List.mem_of_getElem? heLookup
      obtain ⟨heu, hev, hlu, hlv⟩ := hedges edge heMem
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.u heu)
      intro u hu
      have huLookup : components.val[edge.u.val]? = some u := by
        rw [List.getElem?_eq_getElem heu, hu]
      have huEq : u = label edge.u := Option.some.inj (huLookup.symm.trans (hlabels edge.u heu))
      rw [huEq]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec components edge.v hev)
      intro v hv
      have hvLookup : components.val[edge.v.val]? = some v := by
        rw [List.getElem?_eq_getElem hev, hv]
      have hvEq : v = label edge.v := Option.some.inj (hvLookup.symm.trans (hlabels edge.v hev))
      rw [hvEq]
      have hstep : WP.spec
          (if label edge.u != label edge.v then do
            let (slice, back) ← lift (alloc.vec.Vec.deref_mut current)
            let quotient ← topology.Edge.new (label edge.u) (label edge.v)
            let (status, slice') ← topology.count_edge slice componentCount quotient
            ok (status, back slice')
          else ok ((.Ok () : core.result.Result Unit topology.Error), current))
          (fun output => output.1 = .Ok () ∧ output.2.val.length = counts.val.length ∧
            ∀ j, j < counts.val.length → ∃ value : Usize, output.2.val[j]? = some value ∧
              value.val = constructorQuotientDegreeSlot edges.val label j (index.val + 1)) := by
        by_cases hne : label edge.u = label edge.v
        · simp only [hne, bne_self_eq_false, Bool.false_eq_true, ite_false]
          apply (WP.spec_ok _).mpr
          refine ⟨rfl, hlen, ?_⟩
          intro j hj
          obtain ⟨value, hv, hc⟩ := hcounts j hj
          exact ⟨value, hv, by simpa only [constructorQuotientDegreeSlot, heLookup, hne, ite_true] using hc⟩
        · simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, ite_true,
            alloc.vec.Vec.deref_mut, lift, bind_ok]
          apply WP.spec_bind (constructor_edge_new_spec { u := label edge.u, v := label edge.v })
          intro quotient hquotient
          rw [hquotient]
          let canonical := constructorCanonicalEdge { u := label edge.u, v := label edge.v }
          have hcanonical : canonical.u.val < componentCount.val ∧
              canonical.v.val < componentCount.val ∧ canonical.u ≠ canonical.v := by
            unfold canonical constructorCanonicalEdge
            split
            · exact ⟨hlu, hlv, hne⟩
            · exact ⟨hlv, hlu, Ne.symm hne⟩
          obtain ⟨degreeU, hdu, hduc⟩ := hcounts (canonical.u.val + 1) (by omega)
          obtain ⟨degreeV, hdv, hdvc⟩ := hcounts (canonical.v.val + 1) (by omega)
          have hduw : degreeU.val < Usize.max := by
            have hbound := constructor_quotient_degree_le edges.val label (canonical.u.val + 1) index.val
            have := edges.property
            omega
          have hdvw : degreeV.val < Usize.max := by
            have hbound := constructor_quotient_degree_le edges.val label (canonical.v.val + 1) index.val
            have := edges.property
            omega
          apply WP.spec_bind (constructor_count_edge_accepts current.slice componentCount canonical
            hcanonical.1 hcanonical.2.1 hcanonical.2.2 (by
              simpa only [alloc.vec.Vec.val] using (show componentCount.val + 1 ≤ current.val.length by omega))
            degreeU degreeV hdu hdv hduw hdvw)
          rintro ⟨nextStatus, nextSlice⟩ hs
          dsimp only at hs
          obtain ⟨hok, hslen, nextU, nextV, hnu, hnv, hlu', hlv', hframe⟩ := hs
          apply (WP.spec_ok _).mpr
          refine ⟨hok, ?_, ?_⟩
          · change nextSlice.val.length = counts.val.length
            exact hslen.trans (by simpa only [alloc.vec.Vec.val] using hlen)
          intro j hj
          by_cases hju : j = canonical.u.val + 1
          · subst j
            refine ⟨nextU, hlu', ?_⟩
            simpa only [constructorQuotientDegreeSlot, heLookup, hne, ite_false,
              canonical, true_or, ite_true] using hnu.trans (congrArg (· + 1) hduc)
          · by_cases hjv : j = canonical.v.val + 1
            · subst j
              refine ⟨nextV, hlv', ?_⟩
              simpa only [constructorQuotientDegreeSlot, heLookup, hne, ite_false,
                canonical, or_true, ite_true] using hnv.trans (congrArg (· + 1) hdvc)
            · obtain ⟨value, hv, hc⟩ := hcounts j hj
              refine ⟨value, (hframe j hju hjv).trans hv, ?_⟩
              have hju' : j ≠
                  (constructorCanonicalEdge { u := label edge.u, v := label edge.v }).u.val + 1 := hju
              have hjv' : j ≠
                  (constructorCanonicalEdge { u := label edge.u, v := label edge.v }).v.val + 1 := hjv
              simpa only [constructorQuotientDegreeSlot, heLookup, hne, ite_false,
                hju', hjv', false_or] using hc
      apply WP.spec_bind hstep
      rintro ⟨newStatus, newCounts⟩ ⟨hok, hnewLen, hnewCounts⟩
      dsimp only at hok hnewLen hnewCounts
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := edges.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hn
      have hn' : nextIndex.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      exact ⟨⟨by omega, hok, hnewLen, by simpa only [hn'] using hnewCounts⟩, by omega⟩
    · have he : index.val = edges.val.length := by
        have : ¬ index.val < edges.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hstatus, hlen, by simpa only [he] using hcounts⟩
  · refine ⟨by simp, rfl, rfl, ?_⟩
    intro j hj
    exact ⟨0#usize, hzero j hj, rfl⟩

end Labyrinth
