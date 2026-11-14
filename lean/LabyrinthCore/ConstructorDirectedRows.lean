module
public import LabyrinthCore.ConstructorDirected
public import LabyrinthCore.ConstructorSearch
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def constructorDirectedPairs (offsets neighbors : alloc.vec.Vec Usize) : Nat → List (Nat × Nat)
  | 0 => []
  | cell + 1 =>
    let lo := (offsets.val[cell]?.getD 0#usize).val
    let hi := (offsets.val[cell + 1]?.getD 0#usize).val
    constructorDirectedPairs offsets neighbors cell ++
      constructorDirectedPrefix cell neighbors.val lo (hi - lo)

theorem constructor_usize_index {α : Type*} (values : alloc.vec.Vec α) (index : Nat)
    (hindex : index < values.val.length) : ∃ cell : Usize, cell.val = index := by
  have hwidth : index < 2 ^ UScalarTy.Usize.numBits :=
    lt_trans hindex (by simpa using (alloc.vec.Vec.len values).hBounds)
  exact ⟨UScalar.ofNatCore index hwidth, by simp⟩

theorem constructor_directed_pairs_mem (offsets neighbors : alloc.vec.Vec Usize)
    (upto : Nat) (hbound : upto ≤ offsets.val.length - 1) (edge : Nat × Nat) :
    edge ∈ constructorDirectedPairs offsets neighbors upto ↔
      edge.1 < upto ∧ constructorCsrAdjacent offsets neighbors edge.1 edge.2 := by
  induction upto with
  | zero => simp [constructorDirectedPairs]
  | succ upto ih =>
    have ih := ih (by omega)
    simp only [constructorDirectedPairs, List.mem_append,
      constructor_directed_prefix_mem, ih]
    constructor
    · rintro (⟨hlt, hadj⟩ | ⟨k, hk, value, hv, he⟩)
      · exact ⟨by omega, hadj⟩
      · subst edge
        refine ⟨by omega, by dsimp only; omega, _, ?_, ?_, value, hv, rfl⟩
        · dsimp only
          omega
        · dsimp only
          omega
    · rintro ⟨hlt, hcell, j, hjl, hjh, value, hv, hval⟩
      by_cases he : edge.1 < upto
      · exact Or.inl ⟨he, hcell, j, hjl, hjh, value, hv, hval⟩
      · have hfirst : edge.1 = upto := by omega
        right
        refine ⟨j - (offsets.val[upto]?.getD 0#usize).val, ?_, value, ?_, ?_⟩
        · rw [hfirst] at hjl hjh
          omega
        · have hindex : (offsets.val[upto]?.getD 0#usize).val +
              (j - (offsets.val[upto]?.getD 0#usize).val) = j := by
            rw [hfirst] at hjl
            omega
          simpa only [hindex] using hv
        · exact Prod.ext hfirst hval.symm

theorem constructor_directed_pairs_filter (offsets neighbors : alloc.vec.Vec Usize) (upto : Nat) :
    (constructorDirectedPairs offsets neighbors upto).filter
        (fun edge => decide (edge.1 < edge.2)) = constructorCanonicalPairs offsets neighbors upto := by
  induction upto with
  | zero => rfl
  | succ upto ih =>
    simp only [constructorDirectedPairs, constructorCanonicalPairs, List.filter_append,
      ih, constructor_directed_prefix_filter]

theorem constructor_directed_pairs_length (offsets neighbors : alloc.vec.Vec Usize)
    (hfirst : offsets.val[0]? = some 0#usize)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (upto : Nat) (hbound : upto ≤ offsets.val.length - 1) :
    (constructorDirectedPairs offsets neighbors upto).length =
      (offsets.val[upto]?.getD 0#usize).val := by
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  induction upto with
  | zero => simp [constructorDirectedPairs, hfirst]
  | succ upto ih =>
    obtain ⟨lo, hi, hlo, hhi, hordered, hstorage⟩ := hraw upto (by omega)
    have hprevious := ih (by omega)
    simp only [hlo, Option.getD_some] at hprevious
    simp only [constructorDirectedPairs, hlo, hhi, Option.getD_some, List.length_append]
    rw [constructor_directed_prefix_length _ _ _ _ (by omega), hprevious]
    omega

theorem constructor_directed_pairs_nodup (offsets neighbors : alloc.vec.Vec Usize)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hentries : constructorAllRows offsets neighbors (offsets.val.length - 1))
    (upto : Nat) (hbound : upto ≤ offsets.val.length - 1) :
    (constructorDirectedPairs offsets neighbors upto).Nodup := by
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  induction upto with
  | zero => simp [constructorDirectedPairs]
  | succ upto ih =>
    obtain ⟨lo, hi, hlo, hhi, hordered, hstorage⟩ := hraw upto (by omega)
    obtain ⟨cell, hcell⟩ := constructor_usize_index offsets upto (by omega)
    simp only [constructorDirectedPairs, hlo, hhi, Option.getD_some]
    apply List.nodup_append.mpr
    refine ⟨ih (by omega), ?_, ?_⟩
    · apply constructor_directed_prefix_nodup
      intro i j hij hj value hleft hright
      have hentry := hentries cell (by omega) (lo.val + j)
        (by simpa only [hcell, hlo, Option.getD_some] using (show lo.val ≤ lo.val + j by omega))
        (by simpa only [hcell, hhi, Option.getD_some] using (show lo.val + j < hi.val by omega))
      obtain ⟨actual, hactual, _, _, hnodup, _⟩ := hentry
      have he : actual = value := Option.some.inj (hactual.symm.trans hright)
      subst actual
      apply hnodup (lo.val + i) ?_ (by omega) hleft
      simp only [hcell, hlo, Option.getD_some]
      omega
    · intro earlier hearlier current hcurrent heq
      have he := ((constructor_directed_pairs_mem offsets neighbors upto (by omega) earlier).mp hearlier).1
      obtain ⟨k, hk, value, hv, hcurrentEq⟩ :=
        (constructor_directed_prefix_mem upto neighbors.val lo.val (hi.val - lo.val) current).mp hcurrent
      have hfirst := congrArg Prod.fst (heq.trans hcurrentEq)
      dsimp only at hfirst
      omega

/-- Validated reciprocal simple rows justify the constructor's exact half-adjacency allocation. -/
theorem constructor_csr_canonical_count (offsets neighbors : alloc.vec.Vec Usize)
    (hfirst : offsets.val[0]? = some 0#usize)
    (hlast : offsets.val[offsets.val.length - 1]? = some (alloc.vec.Vec.len neighbors))
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hentries : constructorAllRows offsets neighbors (offsets.val.length - 1)) :
    (constructorCanonicalPairs offsets neighbors (offsets.val.length - 1)).length =
      neighbors.val.length / 2 := by
  let directed := constructorDirectedPairs offsets neighbors (offsets.val.length - 1)
  have hnodup : directed.Nodup :=
    constructor_directed_pairs_nodup offsets neighbors hrows hentries _ le_rfl
  have hlength : directed.length = neighbors.val.length := by
    have h := constructor_directed_pairs_length offsets neighbors hfirst hrows _ le_rfl
    simpa only [hlast, Option.getD_some, alloc.vec.Vec.len_val] using h
  have hentryOfMem : ∀ edge ∈ directed, ∃ cell value : Usize,
      cell.val = edge.1 ∧ value.val = edge.2 ∧ value ≠ cell ∧
      ∃ j, (offsets.val[value.val]?.getD 0#usize).val ≤ j ∧
        j < (offsets.val[value.val + 1]?.getD 0#usize).val ∧
        neighbors.val[j]? = some cell ∧ value.val < offsets.val.length - 1 := by
    intro edge hedge
    obtain ⟨hbound, _, j, hjl, hjh, value, hv, hvalue⟩ :=
      (constructor_directed_pairs_mem offsets neighbors _ le_rfl edge).mp hedge
    obtain ⟨cell, hcell⟩ := constructor_usize_index offsets edge.1 (by omega)
    have hentry := hentries cell (by omega) j
      (by simpa only [hcell] using hjl) (by simpa only [hcell] using hjh)
    obtain ⟨actual, ha, hbounded, hself, _, k, hkl, hkh, hk⟩ := hentry
    have he : actual = value := Option.some.inj (ha.symm.trans hv)
    subst actual
    exact ⟨cell, value, hcell, hvalue, hself, k, hkl, hkh, hk, hbounded⟩
  have hself : ∀ edge ∈ directed, edge.1 ≠ edge.2 := by
    intro edge hedge he
    obtain ⟨cell, value, hc, hv, hne, _⟩ := hentryOfMem edge hedge
    exact hne ((UScalar.eq_equiv _ _).mpr (by omega))
  have hreverse : ∀ edge ∈ directed, edge.swap ∈ directed := by
    intro edge hedge
    obtain ⟨cell, value, hc, hv, _, j, hjl, hjh, hj, hbound⟩ := hentryOfMem edge hedge
    apply (constructor_directed_pairs_mem offsets neighbors _ le_rfl edge.swap).mpr
    refine ⟨by simpa only [Prod.swap, hv] using hbound, ?_⟩
    refine ⟨by simpa only [Prod.swap, hv] using hbound, j, ?_, ?_, cell, hj, ?_⟩
    · simpa only [Prod.swap, hv] using hjl
    · simpa only [Prod.swap, hv] using hjh
    · exact hc
  have hcount := constructor_reciprocal_edge_count directed hnodup hself hreverse
  rw [constructor_directed_pairs_filter, hlength] at hcount
  omega

end Labyrinth
