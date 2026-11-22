module
public import LabyrinthCore.SceneConstructionRequired
public import LabyrinthCore.SceneConstructionSpinning

/-! Scene construction (S2), part 3b: the live-edge loop of `Scene::new`. Starting from an empty
list it keeps exactly the carrier edges that `Layout::doorway` admits under the (all-zero) phase
table. Since `check_routes` ran under the same zero tables, every edge it left in `required` is
live. Partial correctness (`OkPost`), as the doorway's geometry is not shown to be total here. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The edge is kept by the live-edge loop: the doorway returns, and its verdict is `Ok`. -/
def DoorwayLive (L : scene.Layout) (phases next : Slice Std.I32) (e : topology.Edge) : Prop :=
  ∃ r, scene.Layout.doorway L e phases next = ok r ∧ r.ok? = true

theorem doorwayAdmits_live (L : scene.Layout) (phases next : Slice Std.I32) (e : topology.Edge)
    (h : DoorwayAdmits L phases next e) : DoorwayLive L phases next e := by
  obtain ⟨d, hd⟩ := h
  exact ⟨_, hd, rfl⟩

open Classical in
/-- The list of carrier edges among the first `i` that are kept. -/
noncomputable def liveEdgesUpTo (L : scene.Layout) (phases : Slice Std.I32) (i : Nat) :
    List topology.Edge :=
  (L.carrier.edges.val.take i).filter (fun e => decide (DoorwayLive L phases phases e))

open Classical in
theorem scene_new_live_loop_body (L : scene.Layout) (phases : alloc.vec.Vec Std.I32)
    (live : alloc.vec.Vec topology.Edge) (i : Std.Usize)
    (hi : i.val ≤ L.carrier.edges.val.length)
    (hlive : live.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) i.val) :
    OkPost (scene.Scene.new_loop0.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms phases live i)
      (fun y => match y with
        | .cont s => s.2.val ≤ L.carrier.edges.val.length ∧
            s.1.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) s.2.val
        | .done y => y.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases)
            L.carrier.edges.val.length) := by
  unfold scene.Scene.new_loop0.body
  have hedges : topology.Carrier.impl.edges L.carrier =
      ok (alloc.vec.Vec.deref L.carrier.edges) := rfl
  rw [hedges, Std.bind_ok]
  by_cases hlt : i < Slice.len (alloc.vec.Vec.deref L.carrier.edges)
  · simp only [hlt, ↓reduceIte]
    have hlt' : i.val < L.carrier.edges.val.length := by simpa [alloc.vec.Vec.deref] using hlt
    refine okPost_bind (okPost_of_spec
      (Slice.index_usize_spec (alloc.vec.Vec.deref L.carrier.edges) i (by simpa
        [alloc.vec.Vec.deref] using hlt'))) ?_
    intro edge hedge
    have hedge' : L.carrier.edges.val[i.val] = edge := by
      simpa [alloc.vec.Vec.deref] using hedge.symm
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro r hr _
    refine okPost_bind (okPost_of_spec (core.result.Result.is_ok.step_spec r)) ?_
    intro b hb
    have hkeep : b = true ↔ DoorwayLive L (alloc.vec.Vec.deref phases)
        (alloc.vec.Vec.deref phases) edge := by
      rw [hb]
      exact ⟨fun h => ⟨r, hr, h⟩, fun ⟨r', hr', h'⟩ => by
        have : r' = r := by
          have := hr.symm.trans hr'
          simpa using this.symm
        subst this; exact h'⟩
    have htake : L.carrier.edges.val.take (i.val + 1) =
        L.carrier.edges.val.take i.val ++ [edge] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt', hedge']
      simp
    have hnext : liveEdgesUpTo L (alloc.vec.Vec.deref phases) (i.val + 1) =
        liveEdgesUpTo L (alloc.vec.Vec.deref phases) i.val ++
          (if DoorwayLive L (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) edge
            then [edge] else []) := by
      classical
      unfold liveEdgesUpTo
      rw [htake, List.filter_append]
      by_cases hd : DoorwayLive L (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) edge
      · simp [hd]
      · simp [hd]
    have hadd : i.val + 1 ≤ Usize.max := by
      have := L.carrier.edges.property
      scalar_tac
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro live1 hl1 _
      have hv := vec_push_ok _ _ _ hl1
      refine okPost_bind (okPost_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by
        simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) ?_
      intro i3 hi3
      have hi3v : i3.val = i.val + 1 := by simpa using hi3
      refine okPost_ok ⟨by simp only [hi3v]; omega, ?_⟩
      show live1.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) i3.val
      rw [hi3v, hnext, hv, hlive]
      simp [hkeep.mp hbt]
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte, Std.bind_ok]
      refine okPost_bind (okPost_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by
        simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) ?_
      intro i3 hi3
      have hi3v : i3.val = i.val + 1 := by simpa using hi3
      refine okPost_ok ⟨by simp only [hi3v]; omega, ?_⟩
      show live.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) i3.val
      have hnk : ¬ DoorwayLive L (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) edge :=
        fun h => hbt (hkeep.mpr h)
      rw [hi3v, hnext, hlive]
      simp [hnk]
  · simp only [hlt, ↓reduceIte]
    have hn : ¬ i.val < L.carrier.edges.val.length := by simpa [alloc.vec.Vec.deref] using hlt
    have : i.val = L.carrier.edges.val.length := by omega
    refine okPost_ok ?_
    show live.val = _
    rw [hlive, this]

/-- From an empty list, the loop returns exactly the carrier edges the doorway admits under
`phases` (as both the phase and the next table). -/
theorem scene_new_live_loop (L : scene.Layout) (phases : alloc.vec.Vec Std.I32)
    (live : alloc.vec.Vec topology.Edge) (hlive : live.val = []) :
    OkPost (scene.Scene.new_loop0 L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms phases live 0#usize)
      (fun y => ∀ e, e ∈ y.val ↔
        e ∈ L.carrier.edges.val ∧
          DoorwayLive L (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) e) := by
  unfold scene.Scene.new_loop0
  refine okPost_mono (okPost_loop
    (fun s : (alloc.vec.Vec topology.Edge) × Std.Usize => s.2.val ≤ L.carrier.edges.val.length ∧
      s.1.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) s.2.val)
    (fun y => y.val = liveEdgesUpTo L (alloc.vec.Vec.deref phases) L.carrier.edges.val.length)
    _ ?_ (live, 0#usize) ⟨by simp, by simp [hlive, liveEdgesUpTo]⟩) ?_
  · rintro ⟨live, i⟩ ⟨hi, hl⟩
    dsimp only at hi hl
    refine okPost_mono (scene_new_live_loop_body L phases live i hi hl) ?_
    intro y hy
    cases y <;> exact hy
  · intro y hy e
    classical
    rw [hy]
    unfold liveEdgesUpTo
    rw [List.take_length, List.mem_filter]
    simp

/-- Two all-zero tables of the same length are the same table. -/
theorem slice_eq_of_allZero (a b : Slice Std.I32) (ha : AllZeroPhases a.val)
    (hb : AllZeroPhases b.val) (hl : a.val.length = b.val.length) : a = b := by
  apply Slice.ext
  apply List.ext_getElem hl
  intro n h1 h2
  have h1' := ha n _ (List.getElem?_eq_getElem h1)
  have h2' := hb n _ (List.getElem?_eq_getElem h2)
  exact IScalar.eq_of_val_eq (by rw [h1', h2'])

/-- Every edge `check_routes` left in `required` is among the live edges, when both ran under
zero tables: the zeroed tables `check_spinning_portals` hands back are the tables
`check_routes` saw. -/
theorem scene_new_required_subset_live (L : scene.Layout) (phases : alloc.vec.Vec Std.I32)
    (s5 : Slice Std.I32) (required live : alloc.vec.Vec topology.Edge)
    (hz : AllZeroPhases phases.val) (hz5 : AllZeroPhases s5.val)
    (hl : s5.val.length = phases.val.length)
    (hadm : AdmittedList L (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases) required)
    (hin : ∀ e ∈ required.val, e ∈ L.carrier.edges.val)
    (hlive : ∀ e, e ∈ live.val ↔ e ∈ L.carrier.edges.val ∧
      DoorwayLive L (alloc.vec.Vec.deref ({ slice := s5 } : alloc.vec.Vec Std.I32))
        (alloc.vec.Vec.deref ({ slice := s5 } : alloc.vec.Vec Std.I32)) e) :
    ∀ e ∈ required.val, e ∈ live.val := by
  have heq : alloc.vec.Vec.deref ({ slice := s5 } : alloc.vec.Vec Std.I32) =
      alloc.vec.Vec.deref phases := by
    apply slice_eq_of_allZero
    · simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val] using hz5
    · simpa [alloc.vec.Vec.deref] using hz
    · simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val] using hl
  intro e he
  refine (hlive e).mpr ⟨hin e he, ?_⟩
  rw [heq]
  exact doorwayAdmits_live _ _ _ _ (hadm e he)

end Labyrinth
