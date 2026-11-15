module
public import LabyrinthCore.ConstructorQuotientFrontier
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The complete extracted fill loop terminates and every occupied CSR slot contains a genuine
original carrier-edge witness. Row capacities are final incidence counts, not assumed evaluation. -/
theorem constructor_quotient_fill_loop_spec (carrier : topology.Carrier)
    (components : alloc.vec.Vec Usize) (edges : Slice topology.Edge)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (cursor : alloc.vec.Vec Usize) (count : Usize) (label : Usize → Usize)
    (start stop : Usize → Nat) (rowOf : Nat → Usize)
    (hcursorLen : count.val ≤ cursor.val.length)
    (hinitial : ConstructorQuotientCursors edges.val label start 0 count cursor)
    (hlabels : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? = some (label node))
    (hedges : ∀ edge ∈ edges.val,
      edge.u.val < components.val.length ∧ edge.v.val < components.val.length ∧
      (label edge.u).val < count.val ∧ (label edge.v).val < count.val ∧
      carrierEdge carrier edge.u.val edge.v.val)
    (hcapacity : ∀ row : Usize, row.val < count.val →
      start row + constructorQuotientRowCount edges.val label row edges.val.length ≤ stop row)
    (hstorage : ∀ row : Usize, row.val < count.val →
      stop row ≤ neighbors.val.length ∧ stop row ≤ witnesses.val.length)
    (hrows : ∀ row : Usize, row.val < count.val → ∀ slot,
      start row ≤ slot → slot < stop row → rowOf slot = row) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop5 0#usize components edges neighbors witnesses cursor)
      (fun output => output.1.val.length = neighbors.val.length ∧
        output.2.val.length = witnesses.val.length ∧
        ∀ slot, constructorQuotientFilled edges.val label start count edges.val.length slot →
          ∃ value original, output.1.val[slot]? = some value ∧ output.2.val[slot]? = some original ∧
            constructorQuotientSlotWitness carrier label (rowOf slot) value original) := by
  let invariant : Usize × alloc.vec.Vec Usize × alloc.vec.Vec topology.Edge × alloc.vec.Vec Usize → Prop :=
    fun state => state.1.val ≤ edges.val.length ∧
      state.2.1.val.length = neighbors.val.length ∧ state.2.2.1.val.length = witnesses.val.length ∧
      state.2.2.2.val.length = cursor.val.length ∧
      ConstructorQuotientCursors edges.val label start state.1.val count state.2.2.2 ∧
      ∀ slot, constructorQuotientFilled edges.val label start count state.1.val slot →
        ∃ value original, state.2.1.val[slot]? = some value ∧ state.2.2.1.val[slot]? = some original ∧
          constructorQuotientSlotWitness carrier label (rowOf slot) value original
  unfold spanning_tree.Tree.scene_dfs_loop5
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize × alloc.vec.Vec topology.Edge × alloc.vec.Vec Usize =>
      edges.val.length - state.1.val) invariant
  · rintro ⟨index, currentNeighbors, currentWitnesses, currentCursor⟩ hi
    obtain ⟨hindex, hnl, hwl, hcl, hcursor, hwritten⟩ := hi
    dsimp only at hindex hnl hwl hcl hcursor hwritten
    by_cases hmore : index.val < edges.val.length
    · let edge := edges.val[index.val]
      have he : edges.val[index.val]? = some edge := List.getElem?_eq_getElem hmore
      have hem : edge ∈ edges.val := List.mem_of_getElem? he
      obtain ⟨heu, hev, hub, hvb, hedge⟩ := hedges edge hem
      by_cases hsame : label edge.u = label edge.v
      · apply WP.spec_mono (constructor_quotient_fill_internal_spec components edges index
          currentNeighbors currentWitnesses currentCursor edge (label edge.u) hmore he heu hev
          (hlabels edge.u heu) (by simpa only [hsame] using hlabels edge.v hev))
        intro output hout
        obtain ⟨nextIndex, hnext, heq⟩ := hout
        rw [heq]
        dsimp only [invariant]
        refine ⟨⟨by omega, hnl, hwl, hcl, ?_, ?_⟩, by omega⟩
        · simpa only [hnext] using constructor_quotient_cursors_internal edges.val label start
            index.val count currentCursor edge hcursor he hsame
        · intro slot hslot
          apply hwritten slot
          rw [hnext, constructor_quotient_filled_internal edges.val label start count index.val edge he hsame] at hslot
          exact hslot
      · obtain ⟨a, ha, hacount⟩ := hcursor (label edge.u) hub
        obtain ⟨b, hb, hbcount⟩ := hcursor (label edge.v) hvb
        have huc : (label edge.u).val < currentCursor.val.length := by omega
        have hvc : (label edge.v).val < currentCursor.val.length := by omega
        have habound : a.val < stop (label edge.u) := by
          have hs := constructor_quotient_crossing_slot_bound edges.val label start stop index.val edge
            (label edge.u) he hsame (Or.inl rfl) hmore (hcapacity (label edge.u) hub)
          omega
        have hbbound : b.val < stop (label edge.v) := by
          have hs := constructor_quotient_crossing_slot_bound edges.val label start stop index.val edge
            (label edge.v) he hsame (Or.inr rfl) hmore (hcapacity (label edge.v) hvb)
          omega
        have hna : a.val < currentNeighbors.val.length := by have := hstorage (label edge.u) hub; omega
        have hnb : b.val < currentNeighbors.val.length := by have := hstorage (label edge.v) hvb; omega
        have hwa : a.val < currentWitnesses.val.length := by have := hstorage (label edge.u) hub; omega
        have hwb : b.val < currentWitnesses.val.length := by have := hstorage (label edge.v) hvb; omega
        apply WP.spec_mono (constructor_quotient_fill_crossing_spec components edges index currentNeighbors
          currentWitnesses currentCursor edge (label edge.u) (label edge.v) a b hmore he heu hev
          (hlabels edge.u heu) (hlabels edge.v hev) hsame huc hvc ha hb hna hnb hwa hwb)
        intro output hout
        obtain ⟨nextIndex, nextA, nextB, hnext, hnextA, hnextB, heq⟩ := hout
        rw [heq]
        dsimp only [invariant]
        refine ⟨⟨by omega, by simpa using hnl, by simpa using hwl, by simpa using hcl, ?_, ?_⟩, by omega⟩
        · simpa only [hnext] using constructor_quotient_cursors_crossing edges.val label start index.val
            count currentCursor edge (label edge.u) (label edge.v) a b nextA nextB hcursor he rfl rfl
            hsame huc hvc ha hb hnextA hnextB
        · intro slot hslot
          have hfilled := (constructor_quotient_filled_crossing edges.val label start count index.val
            edge (label edge.u) (label edge.v) a.val b.val he rfl rfl hsame hub hvb hacount hbcount slot).mp
              (by simpa only [hnext] using hslot)
          apply constructor_quotient_crossing_witnesses carrier label currentNeighbors currentWitnesses
            edge a b hna hnb hwa hwb hedge rowOf
            (hrows (label edge.u) hub a.val (by omega) habound)
            (hrows (label edge.v) hvb b.val (by omega) hbbound)
            (constructorQuotientFilled edges.val label start count index.val) hwritten slot hfilled
    · have he : index.val = edges.val.length := by omega
      have hnot : ¬ index < Slice.len edges := by simpa using hmore
      unfold spanning_tree.Tree.scene_dfs_loop5.body
      simp only [hnot, ite_false]
      apply (WP.spec_ok _).mpr
      dsimp only
      exact ⟨hnl, hwl, by simpa only [he] using hwritten⟩
  · refine ⟨by simp, rfl, rfl, rfl, hinitial, ?_⟩
    intro slot hslot
    obtain ⟨row, _, hstart, hstop⟩ := hslot
    simp only [UScalar.ofNatCore_val_eq, constructorQuotientRowCount] at hstop
    omega

end Labyrinth
