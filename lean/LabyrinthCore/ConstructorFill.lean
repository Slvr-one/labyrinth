module
public import LabyrinthCore.ConstructorDegree
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- One actual adjacency-building iteration writes both orientations and advances exactly
those two row cursors. The input hypotheses describe storage and indices, not evaluation. -/
theorem constructor_fill_edge_step_spec (edges : Slice topology.Edge) (index : Usize)
    (cursor neighbors : alloc.vec.Vec Usize) (edge : topology.Edge) (uPos vPos : Usize)
    (hi : index.val < edges.val.length) (hedge : edges.val[index.val]? = some edge)
    (hu : edge.u.val < cursor.val.length) (hv : edge.v.val < cursor.val.length)
    (hne : edge.u ≠ edge.v)
    (hcursorU : cursor.val[edge.u.val]? = some uPos)
    (hcursorV : cursor.val[edge.v.val]? = some vPos)
    (huPos : uPos.val < neighbors.val.length) (hvPos : vPos.val < neighbors.val.length) :
    WP.spec (topology.Carrier.from_edges_loop2.body edges index cursor neighbors) (fun result =>
      ∃ nextIndex nextU nextV : Usize,
        nextIndex.val = index.val + 1 ∧ nextU.val = uPos.val + 1 ∧ nextV.val = vPos.val + 1 ∧
        result = cont (nextIndex, (cursor.set edge.u nextU).set edge.v nextV,
          (neighbors.set uPos edge.v).set vPos edge.u)) := by
  have hmore : index < Slice.len edges := by simpa using hi
  have hneVal : edge.u.val ≠ edge.v.val := fun he => hne ((UScalar.eq_equiv _ _).mpr he)
  unfold topology.Carrier.from_edges_loop2.body
  simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (Slice.index_usize_spec edges index hi)
  intro actual ha
  have hlookup : edges.val[index.val]? = some actual := by
    rw [List.getElem?_eq_getElem hi, ha]
  have he : actual = edge := Option.some.inj (hlookup.symm.trans hedge)
  rw [he]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cursor edge.u hu)
  intro actualU hau
  have hlookupU : cursor.val[edge.u.val]? = some actualU := by
    rw [List.getElem?_eq_getElem hu, hau]
  have heU : actualU = uPos := Option.some.inj (hlookupU.symm.trans hcursorU)
  rw [heU]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec neighbors uPos huPos)
  rintro ⟨oldU, backU⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec cursor edge.u hu)
  rintro ⟨oldCursorU, backCursorU⟩ ⟨hcu, rfl⟩
  have hcuEq : oldCursorU = uPos := hcu.trans (hau.symm.trans heU)
  rw [hcuEq]
  apply WP.spec_bind (Usize.add_spec (x := uPos) (y := 1#usize) (by
    have := neighbors.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextU hnu
  have hnuval : nextU.val = uPos.val + 1 := by simpa using hnu
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec (cursor.set edge.u nextU) edge.v (by simpa using hv))
  intro actualV hav
  have hlookupV : (cursor.set edge.u nextU).val[edge.v.val]? = some actualV := by
    rw [List.getElem?_eq_getElem (show edge.v.val < (cursor.set edge.u nextU).val.length by simpa using hv), hav]
  have heV : actualV = vPos := by
    have h := hlookupV
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne hneVal, hcursorV] at h
    exact Option.some.inj h.symm
  rw [heV]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (neighbors.set uPos edge.v) vPos (by
    simpa using hvPos))
  rintro ⟨oldV, backV⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (cursor.set edge.u nextU) edge.v (by
    simpa using hv))
  rintro ⟨oldCursorV, backCursorV⟩ ⟨hcv, rfl⟩
  have hcvEq : oldCursorV = vPos := hcv.trans (hav.symm.trans heV)
  rw [hcvEq]
  apply WP.spec_bind (Usize.add_spec (x := vPos) (y := 1#usize) (by
    have := neighbors.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextV hnv
  have hnvval : nextV.val = vPos.val + 1 := by simpa using hnv
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
    have := edges.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextIndex hni
  apply (WP.spec_ok _).mpr
  exact ⟨nextIndex, nextU, nextV, by simpa using hni, hnuval, hnvval, rfl⟩

/-- The row cursor advances once per incident input edge, including parallel inputs. -/
theorem constructor_degree_slot_mono (edges : List topology.Edge) (slot : Nat)
    {a b : Nat} (h : a ≤ b) :
    constructorDegreeSlot edges slot a ≤ constructorDegreeSlot edges slot b := by
  induction h with
  | refl => exact le_rfl
  | @step b h ih =>
    apply le_trans ih
    simp only [constructorDegreeSlot]
    split
    · exact le_rfl
    · split <;> omega

/-- Pure adjacency writes at input-derived row starts and incidence ranks. This is a
mathematical list function, not a hypothesis about the generated computation's result. -/
def constructorFilledNeighbors (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) : Nat → List Usize
  | 0 => initial
  | count + 1 =>
    let previous := constructorFilledNeighbors edges starts initial count
    match edges[count]? with
    | none => previous
    | some edge =>
      (previous.set (starts edge.u.val + constructorDegreeSlot edges (edge.u.val + 1) count)
        edge.v).set (starts edge.v.val + constructorDegreeSlot edges (edge.v.val + 1) count)
        edge.u

theorem constructor_filled_neighbors_length (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (count : Nat) :
    (constructorFilledNeighbors edges starts initial count).length = initial.length := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [constructorFilledNeighbors]
    split <;> simpa only [List.length_set] using ih

/-- The full actual fill loop terminates and its output equals the ordered-write model
`constructorFilledNeighbors`. With overlapping rows a later write can overwrite an earlier one;
retention of both orientations of every edge is `constructor_filled_incidence`, which needs
`hseparated`. -/
theorem constructor_fill_edges_spec (edges : Slice topology.Edge)
    (cursor neighbors : alloc.vec.Vec Usize) (starts : Nat → Nat)
    (hedges : ∀ edge ∈ edges.val,
      edge.u.val < cursor.val.length ∧ edge.v.val < cursor.val.length ∧ edge.u ≠ edge.v)
    (hcursor : ∀ cell, cell < cursor.val.length → ∃ value : Usize,
      cursor.val[cell]? = some value ∧ value.val = starts cell)
    (hcapacity : ∀ cell, cell < cursor.val.length →
      starts cell + constructorDegreeSlot edges.val (cell + 1) edges.val.length ≤
        neighbors.val.length) :
    WP.spec (topology.Carrier.from_edges_loop2 edges 0#usize cursor neighbors) (fun output =>
      output.val = constructorFilledNeighbors edges.val starts neighbors.val edges.val.length) := by
  let invariant : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize → Prop := fun state =>
    state.1.val ≤ edges.val.length ∧ state.2.1.val.length = cursor.val.length ∧
    state.2.2.val = constructorFilledNeighbors edges.val starts neighbors.val state.1.val ∧
    ∀ cell, cell < cursor.val.length → ∃ value : Usize,
      state.2.1.val[cell]? = some value ∧
      value.val = starts cell + constructorDegreeSlot edges.val (cell + 1) state.1.val
  unfold topology.Carrier.from_edges_loop2
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize × alloc.vec.Vec Usize =>
      edges.val.length - state.1.val) invariant
  · rintro ⟨index, currentCursor, currentNeighbors⟩ hinv
    obtain ⟨hindex, hcursorLength, hwrites, hpositions⟩ := hinv
    dsimp only at hindex hcursorLength hwrites hpositions
    have hneighborLength : currentNeighbors.val.length = neighbors.val.length := by
      rw [hwrites, constructor_filled_neighbors_length]
    by_cases hmore : index.val < edges.val.length
    · let edge := edges.val[index.val]'hmore
      have hedge : edges.val[index.val]? = some edge := List.getElem?_eq_getElem hmore
      obtain ⟨hu, hv, hne⟩ := hedges edge (List.getElem_mem hmore)
      obtain ⟨uPos, huPos, huValue⟩ := hpositions edge.u.val hu
      obtain ⟨vPos, hvPos, hvValue⟩ := hpositions edge.v.val hv
      have hdegreeU : constructorDegreeSlot edges.val (edge.u.val + 1) (index.val + 1) =
          constructorDegreeSlot edges.val (edge.u.val + 1) index.val + 1 := by
        simp only [constructorDegreeSlot, hedge, true_or, ite_true]
      have hdegreeV : constructorDegreeSlot edges.val (edge.v.val + 1) (index.val + 1) =
          constructorDegreeSlot edges.val (edge.v.val + 1) index.val + 1 := by
        simp only [constructorDegreeSlot, hedge, or_true, ite_true]
      have huBound : uPos.val < currentNeighbors.val.length := by
        have hmono := constructor_degree_slot_mono edges.val (edge.u.val + 1)
          (show index.val + 1 ≤ edges.val.length by omega)
        have hcap := hcapacity edge.u.val hu
        rw [hdegreeU] at hmono
        omega
      have hvBound : vPos.val < currentNeighbors.val.length := by
        have hmono := constructor_degree_slot_mono edges.val (edge.v.val + 1)
          (show index.val + 1 ≤ edges.val.length by omega)
        have hcap := hcapacity edge.v.val hv
        rw [hdegreeV] at hmono
        omega
      apply WP.spec_mono (constructor_fill_edge_step_spec edges index currentCursor
        currentNeighbors edge uPos vPos hmore hedge (by omega) (by omega) hne
        huPos hvPos huBound hvBound)
      intro result hresult
      obtain ⟨next, nextU, nextV, hnext, hnextU, hnextV, rfl⟩ := hresult
      dsimp only [invariant]
      refine ⟨⟨by omega, by simpa using hcursorLength, ?_, ?_⟩, by omega⟩
      · simp only [alloc.vec.Vec.set_val_eq, hnext, constructorFilledNeighbors,
          hedge, hwrites, huValue, hvValue]
      · intro cell hcell
        have hneVal : edge.u.val ≠ edge.v.val := fun he => hne ((UScalar.eq_equiv _ _).mpr he)
        by_cases hcu : cell = edge.u.val
        · subst cell
          refine ⟨nextU, ?_, ?_⟩
          · simp [alloc.vec.Vec.set, Ne.symm hneVal, hcursorLength, hu]
          · rw [hnext, hdegreeU]
            omega
        · by_cases hcv : cell = edge.v.val
          · subst cell
            refine ⟨nextV, ?_, ?_⟩
            · simp [alloc.vec.Vec.set, hcursorLength, hv]
            · rw [hnext, hdegreeV]
              omega
          · obtain ⟨value, hvalue, hval⟩ := hpositions cell hcell
            refine ⟨value, ?_, ?_⟩
            · simpa [alloc.vec.Vec.set, hcu, Ne.symm hcu, hcv, Ne.symm hcv] using hvalue
            · have hslotU : cell + 1 ≠ edge.u.val + 1 := by omega
              have hslotV : cell + 1 ≠ edge.v.val + 1 := by omega
              simpa only [hnext, constructorDegreeSlot, hedge, hslotU, hslotV,
                false_or, ite_false] using hval
    · have hdone : ¬ index < Slice.len edges := by simpa using hmore
      have he : index.val = edges.val.length := by omega
      unfold topology.Carrier.from_edges_loop2.body
      simp only [hdone, ite_false]
      apply (WP.spec_ok _).mpr
      simpa only [he] using hwrites
  · refine ⟨by simp, rfl, rfl, ?_⟩
    intro cell hcell
    simpa only [UScalar.ofNatCore_val_eq, constructorDegreeSlot, Nat.add_zero] using hcursor cell hcell

/-- Every occupied rank in a row comes from an actual incident edge in the input prefix. -/
theorem constructor_degree_rank_witness (edges : List topology.Edge) (cell count rank : Nat)
    (hrank : rank < constructorDegreeSlot edges (cell + 1) count) :
    ∃ index edge, index < count ∧ edges[index]? = some edge ∧
      (cell = edge.u.val ∨ cell = edge.v.val) ∧
      constructorDegreeSlot edges (cell + 1) index = rank := by
  induction count with
  | zero => simp only [constructorDegreeSlot] at hrank; omega
  | succ count ih =>
    cases hedge : edges[count]? with
    | none =>
      simp only [constructorDegreeSlot, hedge] at hrank
      obtain ⟨index, edge, hi, he, hc, hr⟩ := ih hrank
      exact ⟨index, edge, by omega, he, hc, hr⟩
    | some edge =>
      simp only [constructorDegreeSlot, hedge] at hrank
      by_cases hcell : cell + 1 = edge.u.val + 1 ∨ cell + 1 = edge.v.val + 1
      · simp only [hcell, ite_true] at hrank
        by_cases he : rank = constructorDegreeSlot edges (cell + 1) count
        · exact ⟨count, edge, by omega, hedge, by omega, he.symm⟩
        · obtain ⟨index, earlier, hi, hei, hc, hr⟩ := ih (by omega)
          exact ⟨index, earlier, by omega, hei, hc, hr⟩
      · simp only [hcell, ite_false] at hrank
        obtain ⟨index, earlier, hi, hei, hc, hr⟩ := ih hrank
        exact ⟨index, earlier, by omega, hei, hc, hr⟩

/-- An incident edge strictly advances its row rank before every later input index. -/
theorem constructor_incidence_rank_lt (edges : List topology.Edge) (cell i j : Nat)
    (edge : topology.Edge) (hlookup : edges[i]? = some edge)
    (hcell : cell = edge.u.val ∨ cell = edge.v.val) (hij : i < j) :
    constructorDegreeSlot edges (cell + 1) i < constructorDegreeSlot edges (cell + 1) j := by
  have hmono := constructor_degree_slot_mono edges (cell + 1) (show i + 1 ≤ j by omega)
  have hslot : cell + 1 = edge.u.val + 1 ∨ cell + 1 = edge.v.val + 1 := by omega
  simp only [constructorDegreeSlot, hlookup, hslot, ite_true] at hmono
  omega

/-- Disjoint row intervals make incidences from different cells occupy different slots. -/
theorem constructor_incidence_position_ne (edges : List topology.Edge) (starts : Nat → Nat)
    (n a b i j : Nat) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hi : constructorDegreeSlot edges (a + 1) i < constructorDegreeSlot edges (a + 1) edges.length)
    (hj : constructorDegreeSlot edges (b + 1) j < constructorDegreeSlot edges (b + 1) edges.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u) :
    starts a + constructorDegreeSlot edges (a + 1) i ≠
      starts b + constructorDegreeSlot edges (b + 1) j := by
  have h := hseparated a b ha hb hab
  omega

/-- Every original incidence remains at its unique row/rank slot after the full fill.
Together with the rank-witness lemma this covers every slot, not merely sampled edges. -/
theorem constructor_filled_incidence (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (n count : Nat)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u)
    (hcount : count ≤ edges.length) :
    ∀ index edge, index < count → edges[index]? = some edge →
      (constructorFilledNeighbors edges starts initial count)[
        starts edge.u.val + constructorDegreeSlot edges (edge.u.val + 1) index]? = some edge.v ∧
      (constructorFilledNeighbors edges starts initial count)[
        starts edge.v.val + constructorDegreeSlot edges (edge.v.val + 1) index]? = some edge.u := by
  induction count with
  | zero => intro index edge hi _; omega
  | succ count ih =>
    have hc : count < edges.length := by omega
    let last := edges[count]'hc
    have hlast : edges[count]? = some last := List.getElem?_eq_getElem hc
    obtain ⟨hlu, hlv, hlne⟩ := hedges last (List.getElem_mem hc)
    have hlneVal : last.u.val ≠ last.v.val := fun he => hlne ((UScalar.eq_equiv _ _).mpr he)
    have hluRank := constructor_incidence_rank_lt edges last.u.val count edges.length
      last hlast (Or.inl rfl) hc
    have hlvRank := constructor_incidence_rank_lt edges last.v.val count edges.length
      last hlast (Or.inr rfl) hc
    have hlastNe := constructor_incidence_position_ne edges starts n last.u.val last.v.val
      count count hlu hlv hlneVal hluRank hlvRank hseparated
    have hluBound : starts last.u.val + constructorDegreeSlot edges (last.u.val + 1) count <
        (constructorFilledNeighbors edges starts initial count).length := by
      rw [constructor_filled_neighbors_length]
      have hcap := hcapacity last.u.val hlu
      omega
    have hlvBound : starts last.v.val + constructorDegreeSlot edges (last.v.val + 1) count <
        (constructorFilledNeighbors edges starts initial count).length := by
      rw [constructor_filled_neighbors_length]
      have hcap := hcapacity last.v.val hlv
      omega
    intro index edge hi hedge
    simp only [constructorFilledNeighbors, hlast]
    by_cases he : index = count
    · subst index
      have hedgeEq : edge = last := Option.some.inj (hedge.symm.trans hlast)
      subst edge
      constructor
      · simp [hlastNe, Ne.symm hlastNe, hluBound]
      · simp [hlvBound]
    · have hit : index < count := by omega
      have hmem : edge ∈ edges := List.mem_of_getElem? hedge
      obtain ⟨heu, hev, _⟩ := hedges edge hmem
      have heURank := constructor_incidence_rank_lt edges edge.u.val index edges.length
        edge hedge (Or.inl rfl) (by omega)
      have heVRank := constructor_incidence_rank_lt edges edge.v.val index edges.length
        edge hedge (Or.inr rfl) (by omega)
      have hdistinct (a b : Nat) (ha : a < n) (hb : b < n)
          (hincident : a = edge.u.val ∨ a = edge.v.val)
          (haRank : constructorDegreeSlot edges (a + 1) index <
            constructorDegreeSlot edges (a + 1) edges.length)
          (hbRank : constructorDegreeSlot edges (b + 1) count <
            constructorDegreeSlot edges (b + 1) edges.length) :
          starts a + constructorDegreeSlot edges (a + 1) index ≠
            starts b + constructorDegreeSlot edges (b + 1) count := by
        by_cases hab : a = b
        · subst b
          have hlt := constructor_incidence_rank_lt edges a index count edge hedge hincident hit
          omega
        · exact constructor_incidence_position_ne edges starts n a b index count
            ha hb hab haRank hbRank hseparated
      have huu := hdistinct edge.u.val last.u.val heu hlu (Or.inl rfl) heURank hluRank
      have huv := hdistinct edge.u.val last.v.val heu hlv (Or.inl rfl) heURank hlvRank
      have hvu := hdistinct edge.v.val last.u.val hev hlu (Or.inr rfl) heVRank hluRank
      have hvv := hdistinct edge.v.val last.v.val hev hlv (Or.inr rfl) heVRank hlvRank
      obtain ⟨huLookup, hvLookup⟩ := ih (by omega) index edge hit hedge
      constructor
      · simpa [huu, Ne.symm huu, huv, Ne.symm huv] using huLookup
      · simpa [hvu, Ne.symm hvu, hvv, Ne.symm hvv] using hvLookup

/-- The filled row contains exactly the input incidences, including multiplicity in
their input-order ranks. This transfers the complete fill, not just its writes. -/
theorem constructor_filled_row_iff (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (n cell : Nat) (value : Usize)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u) :
    (∃ rank, rank < constructorDegreeSlot edges (cell + 1) edges.length ∧
      (constructorFilledNeighbors edges starts initial edges.length)[starts cell + rank]? =
        some value) ↔
    ∃ edge ∈ edges, (cell = edge.u.val ∧ value = edge.v) ∨
      (cell = edge.v.val ∧ value = edge.u) := by
  have hfilled := constructor_filled_incidence edges starts initial n edges.length
    hedges hcapacity hseparated le_rfl
  constructor
  · rintro ⟨rank, hrank, hvalue⟩
    obtain ⟨index, edge, hi, hedge, hcell, hdegree⟩ :=
      constructor_degree_rank_witness edges cell edges.length rank hrank
    obtain ⟨hu, hv⟩ := hfilled index edge hi hedge
    refine ⟨edge, List.mem_of_getElem? hedge, ?_⟩
    rcases hcell with hcell | hcell
    · left
      refine ⟨hcell, ?_⟩
      rw [← hcell, hdegree] at hu
      exact Option.some.inj (hvalue.symm.trans hu)
    · right
      refine ⟨hcell, ?_⟩
      rw [← hcell, hdegree] at hv
      exact Option.some.inj (hvalue.symm.trans hv)
  · rintro ⟨edge, hedge, hcell⟩
    obtain ⟨index, hi, hget⟩ := List.mem_iff_getElem.mp hedge
    have hlookup : edges[index]? = some edge := by
      rw [List.getElem?_eq_getElem hi, hget]
    obtain ⟨hu, hv⟩ := hfilled index edge hi hlookup
    refine ⟨constructorDegreeSlot edges (cell + 1) index, ?_, ?_⟩
    · apply constructor_incidence_rank_lt edges cell index edges.length edge hlookup
        _ hi
      rcases hcell with ⟨hc, _⟩ | ⟨hc, _⟩
      · exact Or.inl hc
      · exact Or.inr hc
    · rcases hcell with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · simpa only [hc] using hu
      · simpa only [hc] using hv

end Labyrinth
