module
public import LabyrinthCore.SceneReservationInv

/-! Reservations (S5), part 6: `tick`'s active path. Under `ResInv` the two operations
`ScenePublication.lean` left partial cannot fail: `crossing.duration - crossing.elapsed` (because
`elapsed ≤ duration`) and `holds[id] -= 1` (because every counter a crossing holds is positive, with
the multiplicity of the crossing's own record). The walker loop of `tick` is therefore total on a
scene satisfying `ResInv`, and it keeps `ResInv`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem fromU64U32_val (x : Std.U32) : (core.convert.num.FromU64U32.from x).val = x.val := by
  have hx : x.val < 2 ^ 32 := by have := x.hBounds; scalar_tac
  simp only [core.convert.num.FromU64U32.from, UScalar.val, BitVec.toNat_setWidth]
  simp
  omega

/-- The walker after its crossing ended: in the target cell and pose, ready. -/
def doneWalker (c : walker.Crossing) : walker.Walker :=
  { cell := c.target, «local» := c.target_pose, state := walker.WalkerState.Ready }

/-- The walker one tick later, still crossing, with its elapsed time advanced. -/
def stepWalker (w : walker.Walker) (c : walker.Crossing) (e : Std.U32) : walker.Walker :=
  { cell := w.cell, «local» := w.local, state := walker.WalkerState.Crossing { c with elapsed := e } }

theorem tick_loop0_spec (delta : Std.U64) :
    ∀ (v : alloc.vec.Vec Std.Usize) (v1 : alloc.vec.Vec walker.Walker) (w : Std.Usize),
      w.val ≤ v1.val.length → ResInvL v1.val v.val →
      scene.Scene.tick_loop0 v v1 delta w ⦃ r =>
        ResInvL r.2.val r.1.val ∧ r.2.val.length = v1.val.length ∧
        r.1.val.length = v.val.length ⦄ := by
  intro v0 v10 w0 hw0 hinv0
  unfold scene.Scene.tick_loop0
  refine loop.spec_decr_nat
    (fun s : alloc.vec.Vec Std.Usize × alloc.vec.Vec walker.Walker × Std.Usize =>
      v10.val.length - s.2.2.val)
    (fun s => s.2.2.val ≤ v10.val.length ∧ s.2.1.val.length = v10.val.length ∧
      s.1.val.length = v0.val.length ∧ ResInvL s.2.1.val s.1.val)
    (fun r : alloc.vec.Vec Std.Usize × alloc.vec.Vec walker.Walker =>
      ResInvL r.2.val r.1.val ∧ r.2.val.length = v10.val.length ∧
      r.1.val.length = v0.val.length) _ _ ?_ ⟨hw0, rfl, rfl, hinv0⟩
  rintro ⟨v, v1, w⟩ ⟨hw, hlen1, hlenv, hinv⟩
  simp only at hw hlen1 hlenv hinv
  unfold scene.Scene.tick_loop0.body
  by_cases hlt : w < alloc.vec.Vec.len v1
  · simp only [hlt, ↓reduceIte]
    have hl : w.val < v1.val.length := hlt
    simp only [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec v1 w hl)
    intro w1 hw1
    have hw1s : v1.val[w.val]? = some w1 := by rw [List.getElem?_eq_getElem hl, hw1]
    cases hs : w1.state with
    | Crossing c =>
      obtain ⟨hel, hin, hcell⟩ := hinv.1 w1 (List.mem_of_getElem? hw1s) c hs
      apply spec_bind (Std.U32.sub_spec (x := c.duration) (y := c.elapsed) hel)
      intro i1 hi1
      simp only [lift, Std.bind_ok]
      have hrem : (core.convert.num.FromU64U32.from i1).val = c.duration.val - c.elapsed.val := by
        rw [fromU64U32_val]; exact hi1.1
      have hmult : walkerMult w1 = holdMult c.holds := by
        funext k; simp [walkerMult, hs]
      have hv1w : ∀ k, holdMult c.holds k ≤ crossMult v1.val k := fun k => by
        have := walkerMult_le_crossMult (List.mem_of_getElem? hw1s) k
        rwa [hmult] at this
      by_cases hge : delta ≥ core.convert.num.FromU64U32.from i1
      · simp only [hge, ↓reduceIte]
        simp only [alloc.vec.Vec.index_mut_slice_index]
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec v1 w hl)
        rintro ⟨w2, back⟩ ⟨hw2, hback⟩
        subst hback
        have hl2 : w.val < (v1.set w
            { cell := c.target, «local» := w2.local, state := w2.state } : alloc.vec.Vec _).val.length := by
          simp [alloc.vec.Vec.set_val_eq]; omega
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec _ w hl2)
        rintro ⟨w3, back1⟩ ⟨hw3, hback1⟩
        subst hback1
        have hl3 : w.val < ((v1.set w
            { cell := c.target, «local» := w2.local, state := w2.state }).set w
            { cell := w3.cell, «local» := c.target_pose, state := w3.state } :
              alloc.vec.Vec _).val.length := by
          simp [alloc.vec.Vec.set_val_eq]; omega
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec _ w hl3)
        rintro ⟨w4, back2⟩ ⟨hw4, hback2⟩
        subst hback2
        have hw2' : w2 = w1 := hw2.trans hw1.symm
        subst hw2'
        have hw3' : w3 = { cell := c.target, «local» := w2.local, state := w2.state } := by
          rw [hw3]; simp [alloc.vec.Vec.set_val_eq]
        have hw4' : w4 = { cell := w3.cell, «local» := c.target_pose, state := w3.state } := by
          rw [hw4]; simp [alloc.vec.Vec.set_val_eq]
        have hfinal : (((v1.set w { cell := c.target, «local» := w2.local, state := w2.state }).set w
            { cell := w3.cell, «local» := c.target_pose, state := w3.state }).set w
            { cell := w4.cell, «local» := w4.local, state := walker.WalkerState.Ready } :
              alloc.vec.Vec walker.Walker).val =
            v1.val.set w.val (doneWalker c) := by
          simp [alloc.vec.Vec.set_val_eq, List.set_set, hw3', hw4', doneWalker]
        have hcover : ∀ k, k < v.val.length → ∃ b, v.val[k]? = some b ∧
            holdMult c.holds k ≤ b.val := by
          intro k hk
          obtain ⟨a, ha, hle⟩ := hinv.2 k hk
          exact ⟨a, ha, le_trans (hv1w k) hle⟩
        apply spec_bind (release_loop_spec v c.holds hin hcover v 0#usize (by simp)
          ⟨rfl, fun k hk => by
            obtain ⟨a, ha⟩ : ∃ a, v.val[k]? = some a := ⟨_, List.getElem?_eq_getElem hk⟩
            exact ⟨a, a, ha, ha, by simp [prefMult_zero]⟩⟩)
        intro r hr
        apply spec_bind (usize_succ_spec w (by have := v10.property; scalar_tac))
        intro w5 hw5
        rw [spec_ok]
        have hw5v : w5.val = w.val + 1 := hw5
        have hrl : r.val.length = v.val.length := hr.1
        have hcnt : c.holds.count.val ≤ 4 := hin.1
        refine ⟨⟨by show w5.val ≤ v10.val.length; omega, ?_, ?_, ?_⟩,
          by show _ - w5.val < _ - w.val; omega⟩
        · rw [hfinal]; simp [hlen1]
        · rw [hrl, hlenv]
        · rw [hfinal]
          refine ⟨?_, ?_⟩
          · intro x hx c' hc'
            rw [hrl]
            rcases List.mem_or_eq_of_mem_set hx with hx | rfl
            · exact hinv.1 x hx c' hc'
            · simp [doneWalker] at hc'
          · intro k hk
            rw [hrl] at hk
            obtain ⟨a, b, ha, hb, hab⟩ := hr.2 k hk
            rw [prefMult_full c.holds k hcnt] at hab
            obtain ⟨b', hb', hle⟩ := hinv.2 k hk
            rw [hb] at hb'; cases hb'
            refine ⟨a, ha, ?_⟩
            have hset := crossMult_set v1.val w.val (doneWalker c) k w2 hw1s
            have h0 : walkerMult (doneWalker c) k = 0 := by simp [walkerMult, doneWalker]
            rw [h0, hmult] at hset
            omega
      · have hlt' : delta.val < c.duration.val - c.elapsed.val := by
          have : ¬ (core.convert.num.FromU64U32.from i1).val ≤ delta.val :=
            fun h => hge ((UScalar.le_equiv _ _).mpr h)
          omega
        have hdur : c.duration.val ≤ U32.max := by have := c.duration.hBounds; scalar_tac
        have hcast : (UScalar.cast UScalarTy.U32 delta).val = delta.val := by
          rw [UScalar.cast_val_eq]
          have h32 : delta.val < 2 ^ UScalarTy.U32.numBits := by
            simp only [UScalarTy.numBits]
            have : U32.max = 2 ^ 32 - 1 := by scalar_tac
            omega
          exact Nat.mod_eq_of_lt h32
        simp only [hge, ↓reduceIte]
        apply spec_bind (Std.U32.add_spec (x := c.elapsed) (y := UScalar.cast UScalarTy.U32 delta)
          (by rw [hcast]; omega))
        intro i3 hi3
        have hi3v : i3.val = c.elapsed.val + delta.val := by rw [hi3, hcast]
        simp only [alloc.vec.Vec.index_mut_slice_index]
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec v1 w hl)
        rintro ⟨w2, back⟩ ⟨hw2, hback⟩
        subst hback
        have hw2' : w2 = w1 := hw2.trans hw1.symm
        subst hw2'
        apply spec_bind (usize_succ_spec w (by have := v10.property; scalar_tac))
        intro w3 hw3
        rw [spec_ok]
        have hw3v : w3.val = w.val + 1 := hw3
        have hlen : (v1.set w (stepWalker w2 c i3)).val.length = v10.val.length := by
          simp [alloc.vec.Vec.set_val_eq, hlen1]
        refine ⟨⟨by show w3.val ≤ v10.val.length; omega, hlen, hlenv, ?_⟩,
          by show _ - w3.val < _ - w.val; omega⟩
        show ResInvL (v1.set w (stepWalker w2 c i3)).val v.val
        rw [alloc.vec.Vec.set_val_eq]
        refine ⟨?_, ?_⟩
        · intro x hx c' hc'
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hinv.1 x hx c' hc'
          · simp only [stepWalker, walker.WalkerState.Crossing.injEq] at hc'
            subst hc'
            exact ⟨by simp [hi3v]; omega, hin, hcell⟩
        · intro k hk
          obtain ⟨a, ha, hle⟩ := hinv.2 k hk
          refine ⟨a, ha, ?_⟩
          have hset := crossMult_set v1.val w.val (stepWalker w2 c i3) k w2 hw1s
          have h1 : walkerMult (stepWalker w2 c i3) k = walkerMult w2 k := by
            simp [walkerMult, hs, stepWalker]
          rw [h1] at hset
          omega
    | Ready | Parked | Hidden | Terminated =>
      all_goals
        apply spec_bind (usize_succ_spec w (by have := v10.property; scalar_tac))
        intro w2 hw2
        rw [spec_ok]
        have hw2v : w2.val = w.val + 1 := hw2
        have hl10 : w.val < v10.val.length := by omega
        refine ⟨⟨by show w2.val ≤ v10.val.length; omega, hlen1, hlenv, hinv⟩,
          by show _ - w2.val < _ - w.val; omega⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : ¬ w.val < v1.val.length := hlt
    exact ⟨hinv, hlen1, hlenv⟩

/-! ### The reform loop of `tick` and `drain_patches` only ever stop walkers crossing -/

/-- Every walker of `ws'` is the walker of `ws` at its index, or one that is not crossing. -/
def RelaxedList (ws ws' : List walker.Walker) : Prop :=
  ws'.length = ws.length ∧ ∀ i, i < ws.length → ∃ o n, ws[i]? = some o ∧ ws'[i]? = some n ∧
    (n = o ∨ ∀ c, n.state ≠ walker.WalkerState.Crossing c)

theorem relaxed_refl (ws : List walker.Walker) : RelaxedList ws ws :=
  ⟨rfl, fun i hi => by
    obtain ⟨o, ho⟩ : ∃ o, ws[i]? = some o := ⟨_, List.getElem?_eq_getElem hi⟩
    exact ⟨o, o, ho, ho, Or.inl rfl⟩⟩

theorem relaxed_trans {a b c : List walker.Walker} (h1 : RelaxedList a b) (h2 : RelaxedList b c) :
    RelaxedList a c := by
  obtain ⟨hl1, h1'⟩ := h1
  obtain ⟨hl2, h2'⟩ := h2
  refine ⟨hl2.trans hl1, fun i hi => ?_⟩
  obtain ⟨o, m, ho, hm, hr1⟩ := h1' i hi
  obtain ⟨m', n, hm', hn, hr2⟩ := h2' i (by omega)
  rw [hm] at hm'; cases hm'
  refine ⟨o, n, ho, hn, ?_⟩
  rcases hr2 with h | h
  · subst h; exact hr1
  · exact Or.inr h

theorem relaxed_set (ws y : List walker.Walker) (h : RelaxedList ws y) (i : Nat)
    (a : walker.Walker) (hi : i < ws.length) (ha : ∀ c, a.state ≠ walker.WalkerState.Crossing c) :
    RelaxedList ws (y.set i a) := by
  obtain ⟨hl, h2⟩ := h
  refine ⟨by simp [hl], fun j hj => ?_⟩
  obtain ⟨o, n, ho, hn, hr⟩ := h2 j hj
  by_cases hji : j = i
  · subst hji
    exact ⟨o, a, ho, by rw [List.getElem?_set_self (by omega)], Or.inr ha⟩
  · exact ⟨o, n, ho, by rw [List.getElem?_set_ne (Ne.symm hji)]; exact hn, hr⟩

/-- The reform loop sets covered walkers to `Ready`. -/
theorem tick_ready_relaxed (ws : alloc.vec.Vec walker.Walker) (v1 : alloc.vec.Vec shatter.Patch)
    (p : Std.Usize) :
    ∀ (y : alloc.vec.Vec walker.Walker) (w : Std.Usize), RelaxedList ws.val y.val →
      OkPost (scene.Scene.tick_loop1_loop0 y v1 p w) (fun r => RelaxedList ws.val r.val) := by
  intro y w hy
  unfold scene.Scene.tick_loop1_loop0
  refine okPost_loop (fun s : alloc.vec.Vec walker.Walker × Std.Usize => RelaxedList ws.val s.1.val)
    (fun r : alloc.vec.Vec walker.Walker => RelaxedList ws.val r.val) _ ?_ (y, w) hy
  rintro ⟨y, w⟩ hy
  simp only at hy
  unfold scene.Scene.tick_loop1_loop0.body
  by_cases hlt : w < alloc.vec.Vec.len y
  · simp only [hlt, ↓reduceIte]
    have hl : w.val < y.val.length := hlt
    refine okPost_bind (okPost_trivial _) ?_
    intro p1 _
    refine okPost_bind (okPost_trivial _) ?_
    intro w1 _
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    refine okPost_bind (P := fun v2 : alloc.vec.Vec walker.Walker => RelaxedList ws.val v2.val)
      ?_ ?_
    swap
    · intro v2 hv2
      refine okPost_bind (okPost_trivial _) ?_
      intro w2 _
      exact okPost_ok hv2
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      simp only [alloc.vec.Vec.index_mut_slice_index]
      refine okPost_bind (okPost_of_spec (alloc.vec.Vec.index_mut_usize_spec y w hl)) ?_
      rintro ⟨w2, back⟩ ⟨hw2, hback⟩
      subst hback
      refine okPost_ok ?_
      show RelaxedList ws.val (y.set w { w2 with state := walker.WalkerState.Ready }).val
      rw [alloc.vec.Vec.set_val_eq]
      exact relaxed_set ws.val y.val hy w.val _ (by have := hy.1; omega) (by simp)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hy
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hy

/-- `drain_patches` only parks walkers: the walker list is relaxed. -/
theorem drain_patches_relaxed (x : scene.Scene) (hcs : CrossAtSource x.walkers.val) :
    scene.Scene.drain_patches x ⦃ y =>
      ∃ cw cp, y = { x with walkers := cw, patches := cp } ∧
        RelaxedList x.walkers.val cw.val ⦄ := by
  refine spec_mono (drain_patches_spec x hcs) ?_
  rintro y ⟨cw, cp, hy, hl, _, _, hw⟩
  refine ⟨cw, cp, hy, hl, fun i hi => ?_⟩
  obtain ⟨o, ho, hco⟩ := hw i hi
  refine ⟨o, _, ho, hco, ?_⟩
  unfold drainW
  split
  · right; intro c; simp [parkedWalker]
  · left; rfl

/-- The reforming loop of `tick` only readies walkers. -/
theorem tick_loop1_relaxed (clock : Std.U64) (x : scene.Scene) :
    OkPost (scene.Scene.tick_loop1 x clock 0#usize) (fun y =>
      ∃ cw cp, y = sceneFields { x with walkers := cw, patches := cp } ∧
        RelaxedList x.walkers.val cw.val) := by
  unfold scene.Scene.tick_loop1
  refine okPost_loop (fun s : scene.Scene × Std.Usize =>
      ∃ cw cp, s.1 = { x with walkers := cw, patches := cp } ∧ RelaxedList x.walkers.val cw.val)
    _ _ ?_ (x, 0#usize) ⟨x.walkers, x.patches, rfl, relaxed_refl _⟩
  rintro ⟨s, p⟩ ⟨cw, cp, rfl, hrel⟩
  unfold scene.Scene.tick_loop1.body
  by_cases hlt : p < alloc.vec.Vec.len ({ x with walkers := cw, patches := cp } : scene.Scene).patches
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro p1 _
    cases hst : p1.stage with
    | Reforming u =>
      by_cases hge : clock ≥ u
      · simp only [hge, ↓reduceIte]
        refine okPost_bind (tick_ready_relaxed ({ x with walkers := cw, patches := cp } :
          scene.Scene).walkers cp p cw 0#usize (relaxed_refl _)) ?_
        intro v hv
        refine okPost_bind (okPost_trivial _) ?_
        rintro ⟨p2, back⟩ _
        refine okPost_bind (okPost_trivial _) ?_
        intro p3 _
        refine okPost_ok ?_
        exact ⟨v, _, rfl, relaxed_trans hrel hv⟩
      · simp only [hge, ↓reduceIte]
        refine okPost_bind (okPost_trivial _) ?_
        intro p2 _
        exact okPost_ok ⟨cw, cp, rfl, hrel⟩
    | _ =>
      all_goals
        refine okPost_bind (okPost_trivial _) ?_
        intro p2 _
        exact okPost_ok ⟨cw, cp, rfl, hrel⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok ⟨cw, cp, rfl, hrel⟩

/-- `tick` on its active path keeps the reservation invariant. -/
theorem tick_active_resinv (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampPass self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max) (hinv : ResInv self) :
    OkPost (scene.Scene.tick self stamp wall) (fun res => ResInv res.2) := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  rw [he]
  have hnw : ¬ wall < self.wall := by simpa using hw
  have hsub := Std.U64.sub_spec (x := wall) (y := self.wall) (by scalar_tac)
  obtain ⟨d, hd, hdv⟩ := spec_eq_ok hsub
  simp [core.result.Result.Insts.CoreOpsTry.branch, hnw, hs, hi, hp, hr,
    core.option.Option.is_some, hd]
  have hc := U64.checked_add_bv_spec self.clock d
  cases hco : U64.checked_add self.clock d with
  | none =>
    rw [hco] at hc
    simp at hc
    omega
  | some z =>
    rw [hco] at hc
    simp at hc
    simp only [lift, bind_ok, core.option.Option.ok_or]
    refine okPost_bind (okPost_of_spec (tick_loop0_spec d self.holds self.walkers 0#usize
      (by simp) hinv)) ?_
    rintro ⟨hold, walk⟩ ⟨hinv1, hl1, hl2⟩
    refine okPost_bind (okPost_of_spec (drain_patches_relaxed _ (fun wk hwk c hc =>
      (hinv1.1 wk hwk c hc).2.2))) ?_
    rintro self1 ⟨cw, cp, rfl, hrel⟩
    refine okPost_bind (tick_loop1_relaxed z _) ?_
    rintro ⟨l, t, w, v2, v3, v4, v5, v6, v7, v8, s, i, i1, b1, b2, b3, i2, o1, i3⟩
      ⟨cw2, cp2, hy, hrel2⟩
    simp only [sceneFields, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩ := hy
    refine okPost_ok ?_
    have hrt := relaxed_trans hrel hrel2
    exact resInvL_relaxed _ _ _ hinv1 hrt.1 hrt.2

/-- Under `ResInv` the subtraction `duration - elapsed` of a crossing walker does not fail. -/
theorem resInv_remaining_ok (self : scene.Scene) (hinv : ResInv self) (w : walker.Walker)
    (hw : w ∈ self.walkers.val) (c : walker.Crossing)
    (hc : w.state = walker.WalkerState.Crossing c) :
    (c.duration - c.elapsed) ⦃ z => z.val = c.duration.val - c.elapsed.val ⦄ := by
  have hel := (hinv.1 w hw c hc).1
  refine spec_mono (Std.U32.sub_spec (x := c.duration) (y := c.elapsed) hel) ?_
  intro z hz; exact hz.1

/-- Under `ResInv` every counter a crossing holds is positive, so its decrement in `tick` does not
fail: the id indexes the table and the counter is at least the number of holds on it. -/
theorem resInv_held_positive (self : scene.Scene) (hinv : ResInv self) (w : walker.Walker)
    (hw : w ∈ self.walkers.val) (c : walker.Crossing)
    (hc : w.state = walker.WalkerState.Crossing c) (x : Std.Usize)
    (hx : x ∈ c.holds.ids.val.take c.holds.count.val) :
    ∃ a, self.holds.val[x.val]? = some a ∧ 1 ≤ a.val := by
  obtain ⟨_, hin, _⟩ := hinv.1 w hw c hc
  have hxl : x.val < self.holds.val.length := hin.2 x hx
  obtain ⟨a, ha, hle⟩ := hinv.2 x.val hxl
  refine ⟨a, ha, ?_⟩
  have h1 := walkerMult_le_crossMult hw x.val
  have h2 : 1 ≤ holdMult c.holds x.val := by
    unfold holdMult
    apply List.countP_pos_iff.mpr
    exact ⟨x, hx, by simp⟩
  have h3 : walkerMult w x.val = holdMult c.holds x.val := by simp [walkerMult, hc]
  omega

end Labyrinth
