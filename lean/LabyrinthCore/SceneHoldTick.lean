module
public import LabyrinthCore.SceneHoldLaw

/-! The hold law, part 2: the walker loop of `tick` releases exactly what each ending crossing holds.

The loop either ends a crossing (the walker moves to its target, becomes `Ready`, and each held
counter is decremented once per hold) or advances it (same ends, corridor and holds). So the counters
stay equal to the crossing-holds, and every crossing after the loop is a crossing from before it. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Replacing an entry by a walker whose crossings come from the list keeps `CrossSub`. -/
theorem crossSub_set {a b : List walker.Walker} (h : CrossSub a b) (i : Nat) (n : walker.Walker)
    (hn : ∀ c', n.state = walker.WalkerState.Crossing c' →
      ∃ m ∈ b, ∃ c, m.state = walker.WalkerState.Crossing c ∧ c.source = c'.source ∧
        c.target = c'.target ∧ c.corridor = c'.corridor ∧ c.holds = c'.holds) :
    CrossSub a (b.set i n) := by
  intro x hx c' hc'
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx c' hc'
  · obtain ⟨m, hm, c, hc, e1, e2, e3, e4⟩ := hn c' hc'
    obtain ⟨o, ho, co, hco, f1, f2, f3, f4⟩ := h m hm c hc
    exact ⟨o, ho, co, hco, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4⟩

/-- **The walker loop of `tick`, exactly.** -/
theorem tick_loop0_exact (delta : Std.U64) :
    ∀ (v : alloc.vec.Vec Std.Usize) (v1 : alloc.vec.Vec walker.Walker) (w : Std.Usize),
      w.val ≤ v1.val.length → ResInvL v1.val v.val →
      scene.Scene.tick_loop0 v v1 delta w ⦃ r =>
        ResInvL r.2.val r.1.val ∧ (HoldEqL v1.val v.val → HoldEqL r.2.val r.1.val) ∧
        CrossSub v1.val r.2.val ∧
        r.2.val.length = v1.val.length ∧ r.1.val.length = v.val.length ⦄ := by
  intro v0 v10 w0 hw0 hinv0
  unfold scene.Scene.tick_loop0
  refine loop.spec_decr_nat
    (fun s : alloc.vec.Vec Std.Usize × alloc.vec.Vec walker.Walker × Std.Usize =>
      v10.val.length - s.2.2.val)
    (fun s => s.2.2.val ≤ v10.val.length ∧ s.2.1.val.length = v10.val.length ∧
      s.1.val.length = v0.val.length ∧ ResInvL s.2.1.val s.1.val ∧
      (HoldEqL v10.val v0.val → HoldEqL s.2.1.val s.1.val) ∧ CrossSub v10.val s.2.1.val)
    (fun r : alloc.vec.Vec Std.Usize × alloc.vec.Vec walker.Walker =>
      ResInvL r.2.val r.1.val ∧ (HoldEqL v10.val v0.val → HoldEqL r.2.val r.1.val) ∧
      CrossSub v10.val r.2.val ∧
      r.2.val.length = v10.val.length ∧ r.1.val.length = v0.val.length) _ _ ?_
    ⟨hw0, rfl, rfl, hinv0, fun h => h, crossSub_refl _⟩
  rintro ⟨v, v1, w⟩ ⟨hw, hlen1, hlenv, hinv, heq, hsub⟩
  simp only at hw hlen1 hlenv hinv heq hsub
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
        have hdone : ∀ k, crossMult (v1.val.set w.val (doneWalker c)) k + holdMult c.holds k =
            crossMult v1.val k := by
          intro k
          have hset := crossMult_set v1.val w.val (doneWalker c) k w2 hw1s
          have h0 : walkerMult (doneWalker c) k = 0 := by simp [walkerMult, doneWalker]
          rw [h0, hmult] at hset
          omega
        refine ⟨⟨by show w5.val ≤ v10.val.length; omega, ?_, ?_, ?_, ?_, ?_⟩,
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
            have := hdone k
            omega
        · rw [hfinal]
          intro h0 k hk
          rw [hrl] at hk
          obtain ⟨a, b, ha, hb, hab⟩ := hr.2 k hk
          rw [prefMult_full c.holds k hcnt] at hab
          obtain ⟨b', hb', he⟩ := heq h0 k hk
          rw [hb] at hb'; cases hb'
          refine ⟨a, ha, ?_⟩
          have := hdone k
          omega
        · rw [hfinal]
          exact crossSub_set hsub _ _ (fun c' hc' => by simp [doneWalker] at hc')
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
        have hsame : ∀ k, crossMult (v1.val.set w.val (stepWalker w2 c i3)) k = crossMult v1.val k := by
          intro k
          have hset := crossMult_set v1.val w.val (stepWalker w2 c i3) k w2 hw1s
          have h1 : walkerMult (stepWalker w2 c i3) k = walkerMult w2 k := by
            simp [walkerMult, hs, stepWalker]
          rw [h1] at hset
          omega
        refine ⟨⟨by show w3.val ≤ v10.val.length; omega, hlen, hlenv, ?_, ?_, ?_⟩,
          by show _ - w3.val < _ - w.val; omega⟩
        · show ResInvL (v1.set w (stepWalker w2 c i3)).val v.val
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
            exact ⟨a, ha, by rw [hsame k]; exact hle⟩
        · show HoldEqL v10.val v0.val → HoldEqL (v1.set w (stepWalker w2 c i3)).val v.val
          rw [alloc.vec.Vec.set_val_eq]
          intro h0 k hk
          obtain ⟨a, ha, he⟩ := heq h0 k hk
          exact ⟨a, ha, by rw [hsame k]; exact he⟩
        · show CrossSub v10.val (v1.set w (stepWalker w2 c i3)).val
          rw [alloc.vec.Vec.set_val_eq]
          refine crossSub_set hsub _ _ (fun c' hc' => ?_)
          simp only [stepWalker, walker.WalkerState.Crossing.injEq] at hc'
          subst hc'
          exact ⟨w2, List.mem_of_getElem? hw1s, c, hs, rfl, rfl, rfl, rfl⟩
    | Ready | Parked | Hidden | Terminated =>
      all_goals
        apply spec_bind (usize_succ_spec w (by have := v10.property; scalar_tac))
        intro w2 hw2
        rw [spec_ok]
        have hw2v : w2.val = w.val + 1 := hw2
        have hl10 : w.val < v10.val.length := by omega
        refine ⟨⟨by show w2.val ≤ v10.val.length; omega, hlen1, hlenv, hinv, heq, hsub⟩,
          by show _ - w2.val < _ - w.val; omega⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : ¬ w.val < v1.val.length := hlt
    exact ⟨hinv, heq, hsub, hlen1, hlenv⟩

end Labyrinth
