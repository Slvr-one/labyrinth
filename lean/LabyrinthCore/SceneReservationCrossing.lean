module
public import LabyrinthCore.SceneReservationHolds
public import LabyrinthCore.ScenePublication

/-! Reservations (S5), part 3: `Scene::begin_crossing`.

The checks run in this order and the first failure is returned with the scene unchanged:
stamp (`StaleEpoch`, `StaleRevision`, `Overflow`), walker index (`InvalidIndex`), walker not ready
or zero duration (`InvalidTransition`), `admission` of the walker's cell, `admission` of the target,
the edge `{cell, target}` is a tree edge (`InvalidTransition`), `Layout::doorway`, and the capacity
of the held counters (`Overflow`). On success the walker becomes `Crossing` (elapsed `0`, the given
duration, a fresh reservation `{epoch, walker, serial := revision + 1}`), each held counter rises
by its multiplicity, and the revision advances; nothing else changes.

The call reaches `Layout::doorway`, so the statement is partial correctness (`OkPost`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem okPost_ok_iff {α : Type _} {P : α → Prop} {a : α} : OkPost (ok a) P ↔ P a :=
  ⟨fun h => h a rfl, okPost_ok⟩

/-- The partial-correctness form of `stamp_gate`. -/
theorem stamp_gate_ok {α : Type _} (self : scene.Scene) (stamp : walker.Stamp)
    (K : Std.U64 → Result (core.result.Result α topology.Error × scene.Scene))
    (P : core.result.Result α topology.Error × scene.Scene → Prop)
    (hok : ∀ v : Std.U64, v.val = self.stamp.revision.val + 1 → StampAccepts self stamp →
      OkPost (K v) P)
    (hrej : ∀ res, ¬ StampAccepts self stamp → StampRejects self stamp res → P res) :
    OkPost (do
      let r ← scene.Scene.check_stamp self stamp
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => K val
      | core.ops.control_flow.ControlFlow.Break residual =>
        do
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            α (core.convert.FromSame topology.Error) residual
        ok (r1, self)) P := by
  by_cases h1 : stamp.epoch = self.stamp.epoch
  · by_cases h2 : stamp.revision = self.stamp.revision
    · have hle : self.stamp.revision.val ≤ U64.max := by scalar_tac
      by_cases h3 : self.stamp.revision.val = U64.max
      · rw [check_stamp_overflow self stamp h1 h2 h3]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
        apply hrej _ (fun h => by obtain ⟨_, _, h3'⟩ := h; omega)
        exact ⟨fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ _ => rfl⟩
      · obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 (by omega)
        rw [he]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        exact hok v hv ⟨h1, h2, by omega⟩
    · rw [check_stamp_stale_revision self stamp h1 h2]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
      apply hrej _ (fun h => h2 h.2.1)
      exact ⟨fun h => absurd h1 h, fun _ _ => rfl, fun _ h => absurd h h2⟩
  · rw [check_stamp_stale_epoch self stamp h1]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
    apply hrej _ (fun h => h1 h.1)
    exact ⟨fun _ => rfl, fun h => absurd h h1, fun h => absurd h h1⟩

/-! ### The outcome of `begin_crossing` -/

/-- The walker named by the call is ready and the duration is positive. -/
def BcReady (self : scene.Scene) (wi : Std.Usize) (duration : Std.U32) (w : walker.Walker) : Prop :=
  self.walkers.val[wi.val]? = some w ∧ w.state = walker.WalkerState.Ready ∧ duration ≠ 0#u32

/-- Both cells pass `admission`. -/
def BcAdmitted (self : scene.Scene) (w : walker.Walker) (target : Std.Usize) : Prop :=
  admissionVerdict self w.cell.val = .Ok () ∧ admissionVerdict self target.val = .Ok ()

/-- The edge between the walker's cell and the target is a tree edge. -/
def BcEdge (self : scene.Scene) (w : walker.Walker) (target : Std.Usize) (e : topology.Edge) :
    Prop :=
  topology.Edge.new w.cell target = ok e ∧ parentEdge (parents self.tree) e.u.val e.v.val

/-- The crossing `begin_crossing` stores. -/
def bcCrossing (self : scene.Scene) (w : walker.Walker) (wi target : Std.Usize)
    (duration : Std.U32) (val : Std.U64) (door : scene.Doorway) (path : walker.Path)
    (lp : walker.LocalPose) : walker.Crossing :=
  { source := w.cell, target, elapsed := 0#u32, duration,
    reservation := { epoch := self.stamp.epoch, walker := wi, serial := val },
    corridor := door.corridor, path, target_pose := lp, holds := door.holds }

/-- The scene after a successful `begin_crossing`. -/
def bcAfter (self : scene.Scene) (w : walker.Walker) (wi : Std.Usize) (c : walker.Crossing)
    (val : Std.U64) (newHolds : alloc.vec.Vec Std.Usize) : scene.Scene :=
  { self with
    holds := newHolds
    walkers := alloc.vec.Vec.set self.walkers wi { w with state := walker.WalkerState.Crossing c }
    stamp := { self.stamp with revision := val } }

/-- Everything `begin_crossing` can answer after the stamp passed, in the order of its checks: each
case includes that every earlier check passed. -/
def BcAccepted (self : scene.Scene) (wi target : Std.Usize) (duration : Std.U32)
    (res : core.result.Result walker.Reservation topology.Error × scene.Scene) : Prop :=
  (self.walkers.val.length ≤ wi.val ∧ res = (.Err topology.Error.InvalidIndex, self)) ∨
  (∃ w, self.walkers.val[wi.val]? = some w ∧
    (w.state ≠ walker.WalkerState.Ready ∨ duration = 0#u32) ∧
    res = (.Err topology.Error.InvalidTransition, self)) ∨
  (∃ w, BcReady self wi duration w ∧ ∃ e, admissionVerdict self w.cell.val = .Err e ∧
    res = (.Err e, self)) ∨
  (∃ w, BcReady self wi duration w ∧ admissionVerdict self w.cell.val = .Ok () ∧
    ∃ e, admissionVerdict self target.val = .Err e ∧ res = (.Err e, self)) ∨
  (∃ w e1, BcReady self wi duration w ∧ BcAdmitted self w target ∧
    topology.Edge.new w.cell target = ok e1 ∧
    ¬ parentEdge (parents self.tree) e1.u.val e1.v.val ∧
    res = (.Err topology.Error.InvalidTransition, self)) ∨
  (∃ w e1 x, BcReady self wi duration w ∧ BcAdmitted self w target ∧ BcEdge self w target e1 ∧
    scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
      (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Err x) ∧
    res = (.Err x, self)) ∨
  (∃ w e1 door, BcReady self wi duration w ∧ BcAdmitted self w target ∧ BcEdge self w target e1 ∧
    scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
      (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok door) ∧
    HoldsSaturated door.holds (alloc.vec.Vec.deref self.holds) ∧
    res = (.Err topology.Error.Overflow, self)) ∨
  (∃ (w : walker.Walker) (e1 : topology.Edge) (door : scene.Doorway) (path : walker.Path)
    (lp : walker.LocalPose) (val : Std.U64) (newHolds : alloc.vec.Vec Std.Usize),
    BcReady self wi duration w ∧ BcAdmitted self w target ∧ BcEdge self w target e1 ∧
    scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
      (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok door) ∧
    HoldsCapacity door.holds (alloc.vec.Vec.deref self.holds) ∧
    val.val = self.stamp.revision.val + 1 ∧
    scene.oriented_path door.path (decide (w.cell = e1.u)) = ok path ∧
    scene.Layout.local_pose self.layout target = ok lp ∧
    AddPref self.holds.val newHolds.val door.holds door.holds.count.val ∧
    res = (.Ok { epoch := self.stamp.epoch, walker := wi, serial := val },
      bcAfter self w wi (bcCrossing self w wi target duration val door path lp) val newHolds))

/-- `begin_crossing`: the stamp check, then the accepted cases above. -/
def BcOutcome (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32)
    (res : core.result.Result walker.Reservation topology.Error × scene.Scene) : Prop :=
  (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
  (StampAccepts self stamp ∧ BcAccepted self wi target duration res)

theorem begin_crossing_outcome (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration)
      (BcOutcome self stamp wi target duration) := by
  unfold scene.Scene.begin_crossing
  apply stamp_gate_ok
  · intro val hval hpass
    refine okPost_mono (P := fun res => BcAccepted self wi target duration res) ?_
      (fun res h => Or.inr ⟨hpass, h⟩)
    have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice walker.Walker)
        (alloc.vec.Vec.deref self.walkers) wi = ok (self.walkers.val[wi.val]?) := by
      simp [core.slice.Slice.get, alloc.vec.Vec.deref]
    simp only [hget, Std.bind_ok]
    cases hw : self.walkers.val[wi.val]? with
    | none =>
      have hlen : self.walkers.val.length ≤ wi.val := by
        by_contra h
        have := (List.getElem?_eq_getElem (l := self.walkers.val) (by omega : wi.val <
          self.walkers.val.length))
        rw [hw] at this; simp at this
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
      exact Or.inl ⟨hlen, rfl⟩
    | some w =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hwl := hw
      refine okPost_bind_eq (okPost_of_spec (walkerState_ne_ready w.state)) ?_
      intro b _ hb
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte, okPost_ok_iff]
        exact Or.inr (Or.inl ⟨w, hw, Or.inl (hb.mp hbt), rfl⟩)
      · have hready : w.state = walker.WalkerState.Ready := by
          by_contra hne
          exact hbt (hb.mpr hne)
        simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        by_cases hd : duration = 0#u32
        · simp only [hd, ↓reduceIte, okPost_ok_iff]
          exact Or.inr (Or.inl ⟨w, hw, Or.inr rfl, rfl⟩)
        · simp only [hd, ↓reduceIte]
          have hr : BcReady self wi duration w := ⟨hw, hready, hd⟩
          refine okPost_bind_eq (okPost_of_spec (admission_spec self w.cell)) ?_
          intro r2 _ hr2
          cases r2 with
          | Err e =>
            simp only [Std.bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
            exact Or.inr (Or.inr (Or.inl ⟨w, hr, e, hr2.symm, rfl⟩))
          | Ok u =>
            simp only [Std.bind_ok]
            have hr2' : admissionVerdict self w.cell.val = .Ok () := by rw [← hr2]
            refine okPost_bind_eq (okPost_of_spec (admission_spec self target)) ?_
            intro r3 _ hr3
            cases r3 with
            | Err e =>
              simp only [Std.bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hr, hr2', e, hr3.symm, rfl⟩)))
            | Ok u3 =>
              simp only [Std.bind_ok]
              have hr3' : admissionVerdict self target.val = .Ok () := by rw [← hr3]
              have hadm : BcAdmitted self w target := ⟨hr2', hr3'⟩
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro e1 he1 _
              refine okPost_bind_eq (okPost_of_spec (mutation_has_edge_total self.tree e1)) ?_
              intro b1 _ hb1
              by_cases hb1t : b1 = true
              · simp only [hb1t, ↓reduceIte]
                have hedge : BcEdge self w target e1 := ⟨he1, hb1.mp hb1t⟩
                refine okPost_bind_eq (okPost_trivial _) ?_
                intro r4 hr4 _
                cases r4 with
                | Err x =>
                  simp only [Std.bind_ok,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨w, e1, x, hr, hadm, hedge, hr4, rfl⟩)))))
                | Ok door =>
                  simp only [Std.bind_ok]
                  refine okPost_bind_eq (okPost_trivial _) ?_
                  intro r5 hr5 _
                  have hcap := check_hold_capacity_post door.holds (alloc.vec.Vec.deref self.holds)
                    r5 hr5
                  cases r5 with
                  | Err x =>
                    have hx : x = topology.Error.Overflow := by
                      rcases hcap.2.2 with h | h
                      · simp at h
                      · simpa using h
                    subst hx
                    simp only [Std.bind_ok,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                      core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                      ⟨w, e1, door, hr, hadm, hedge, hr4, hcap.2.1 rfl, rfl⟩))))))
                  | Ok u5 =>
                    simp only [Std.bind_ok]
                    have hcc := hcap.1 rfl
                    refine okPost_bind_eq (okPost_trivial _) ?_
                    intro path hpath _
                    refine okPost_bind_eq (okPost_trivial _) ?_
                    intro lp hlp _
                    simp only [lift, Std.bind_ok, alloc.vec.Vec.deref_mut]
                    refine okPost_bind (acquire_holds_post self.holds.slice door.holds) ?_
                    intro s5 hs5
                    have hbound : wi.val < self.walkers.val.length :=
                      (List.getElem?_eq_some_iff.mp hw).1
                    simp only [alloc.vec.Vec.index_mut_slice_index]
                    refine okPost_bind (okPost_of_spec (alloc.vec.Vec.index_mut_usize_spec
                      self.walkers wi hbound)) ?_
                    rintro ⟨w2, back⟩ ⟨hw2, hback⟩
                    have hww : w2 = w := by
                      rw [List.getElem?_eq_getElem hbound] at hw
                      rw [hw2]; exact Option.some.inj hw
                    subst hww
                    refine okPost_ok ?_
                    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      ⟨w2, e1, door, path, lp, val, { slice := s5 }, hr, hadm, hedge, hr4, hcc,
                        hval, hpath, hlp, ?_, ?_⟩))))))
                    · exact hs5
                    · rw [hback]; rfl
              · simp only [hb1t, Bool.false_eq_true, ↓reduceIte, okPost_ok_iff]
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨w, e1, hr, hadm, he1, fun h => hb1t (hb1.mpr h), rfl⟩))))
  · intro res hn hf
    exact Or.inl ⟨hn, hf⟩

theorem stampFail_scene {α : Type _} {self : scene.Scene} {stamp : walker.Stamp}
    {res : core.result.Result α topology.Error × scene.Scene}
    (hn : ¬ StampAccepts self stamp) (hf : StampRejects self stamp res) : res.2 = self := by
  obtain ⟨f1, f2, f3⟩ := hf
  by_cases h1 : stamp.epoch = self.stamp.epoch
  · by_cases h2 : stamp.revision = self.stamp.revision
    · have h3 : self.stamp.revision.val = U64.max := by
        by_contra h3
        exact hn ⟨h1, h2, by have := self.stamp.revision.hBounds; scalar_tac⟩
      rw [f3 h1 h2 h3]
    · rw [f2 h1 h2]
  · rw [f1 h1]

/-- Every rejection by `begin_crossing` leaves the scene exactly as it was. -/
theorem begin_crossing_rejection_frame (self : scene.Scene) (stamp : walker.Stamp)
    (wi target : Std.Usize) (duration : Std.U32) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration) (fun res =>
      ∀ e, res.1 = core.result.Result.Err e → res.2 = self) := by
  refine okPost_mono (begin_crossing_outcome self stamp wi target duration) ?_
  rintro ⟨r, s'⟩ h e he
  simp only at he ⊢
  subst he
  rcases h with ⟨hn, hf⟩ | ⟨_, h⟩
  · exact stampFail_scene hn hf
  · rcases h with ⟨_, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, e', _, h⟩ | ⟨w, _, _, e', _, h⟩ |
      ⟨w, e1, _, _, _, _, h⟩ | ⟨w, e1, x, _, _, _, _, h⟩ | ⟨w, e1, d, _, _, _, _, _, h⟩ |
      ⟨w, e1, d, p, lp, v, nh, _, _, _, _, _, _, _, _, _, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> first | exact h.2 | (cases h.1)

end Labyrinth
