module
public import LabyrinthCore.SceneShatterBegin
public import LabyrinthCore.SceneReservationTick
public import LabyrinthCore.SceneReservationInv

/-! Shatter (S6), part 6: the reform step of `tick`. For every patch in stage `Reforming { until }`
whose deadline `until` has been reached by the clock, `tick` readies every walker standing in the
patch and sets the patch `Idle`; the other patches are untouched. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The sweep of `tick`'s reform step: every walker standing in the patch is readied. -/
theorem tick_sweep_spec (vw : alloc.vec.Vec walker.Walker) (vp : alloc.vec.Vec shatter.Patch)
    (slot : Std.Usize) (pp : shatter.Patch) (hp : vp.val[slot.val]? = some pp)
    (w0 : Std.Usize) :
    scene.Scene.tick_loop1_loop0 vw vp slot w0 ⦃ r =>
      r.val.length = vw.val.length ∧
      ∀ i, r.val[i]? =
        if w0.val ≤ i then (vw.val[i]?).map (stateIf pp walker.WalkerState.Ready) else
          vw.val[i]? ⦄ := by
  unfold scene.Scene.tick_loop1_loop0
  refine loop.spec_decr_nat (fun x : alloc.vec.Vec walker.Walker × Std.Usize =>
      x.1.val.length - x.2.val)
    (fun x => x.1.val.length = vw.val.length ∧ w0.val ≤ x.2.val ∧
      ∀ i, x.1.val[i]? = if w0.val ≤ i ∧ i < x.2.val then
        (vw.val[i]?).map (stateIf pp walker.WalkerState.Ready) else vw.val[i]?)
    (fun r : alloc.vec.Vec walker.Walker => r.val.length = vw.val.length ∧
      ∀ i, r.val[i]? =
        if w0.val ≤ i then (vw.val[i]?).map (stateIf pp walker.WalkerState.Ready) else
          vw.val[i]?)
    _ (vw, w0) ?_ ⟨rfl, le_refl _, fun i => by simp⟩
  rintro ⟨y, w⟩ ⟨hl, hw0, hy⟩
  dsimp only at hl hw0 hy
  unfold scene.Scene.tick_loop1_loop0.body
  by_cases hlt : w < alloc.vec.Vec.len y
  · have hltn : w.val < y.val.length := by simpa using hlt
    simp only [hlt, ↓reduceIte]
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    have hpl : slot.val < vp.val.length := (List.getElem?_eq_some_iff.mp hp).1
    apply spec_bind (alloc.vec.Vec.index_usize_spec vp slot hpl)
    intro p1 hp1
    have hpe : p1 = pp := by
      rw [hp1]
      have := hp
      rw [List.getElem?_eq_getElem hpl] at this
      exact Option.some.inj this
    apply spec_bind (alloc.vec.Vec.index_usize_spec y w hltn)
    intro w1 hw1
    apply spec_bind (patch_contains_spec p1 w1.cell)
    intro b hb
    rw [hpe] at hb
    have hyw : y.val[w.val]? = some w1 := by
      rw [List.getElem?_eq_getElem hltn]; simp [hw1]
    have hoyw : vw.val[w.val]? = some w1 := by
      have := hy w.val
      simp only [show ¬ (w0.val ≤ w.val ∧ w.val < w.val) from by omega, ↓reduceIte] at this
      rw [hyw] at this
      exact this.symm
    by_cases hbt : b = true
    · have hhas : PatchHas pp w1.cell.val := hb.mp hbt
      simp only [hbt, ↓reduceIte, Std.bind_assoc]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec y w hltn)
      rintro ⟨w2, back⟩ ⟨hw2, hback⟩
      subst hback
      erw [Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := w) (y := 1#usize) (by scalar_tac))
      intro w3 hw3
      have hw3v : w3.val = w.val + 1 := by simpa using hw3
      rw [spec_ok]; dsimp only
      refine ⟨⟨by simp [hl, alloc.vec.Vec.set_val_eq], by omega, fun i => ?_⟩, by simp only [alloc.vec.Vec.set_val_eq, List.length_set]; omega⟩
      rw [hw3v]
      rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases hiw : w.val = i
      · subst hiw
        have hw2e : w2 = w1 := by rw [hw2] at *; simp [hw1] at hw2 ⊢
        subst hw2e
        simp only [hltn, hoyw, true_and, ↓reduceIte, Option.map_some, stateIf, hhas,
          show w0.val ≤ w.val ∧ w.val < w.val + 1 from ⟨by omega, by omega⟩]
      · simp only [hiw, ↓reduceIte]
        rw [hy i]
        have : (w0.val ≤ i ∧ i < w.val) ↔ (w0.val ≤ i ∧ i < w.val + 1) := by omega
        simp only [this]
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte, Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := w) (y := 1#usize) (by scalar_tac))
      intro w3 hw3
      have hw3v : w3.val = w.val + 1 := by simpa using hw3
      have hnh : ¬ PatchHas pp w1.cell.val := fun h => hbt (hb.mpr h)
      rw [spec_ok]; dsimp only
      refine ⟨⟨hl, by omega, fun i => ?_⟩, by omega⟩
      rw [hw3v]
      rw [hy i]
      by_cases hiw : w.val = i
      · subst hiw
        simp only [hoyw, stateIf, hnh, ↓reduceIte, Option.map_some,
          show w0.val ≤ w.val ∧ w.val < w.val + 1 from ⟨by omega, by omega⟩]
        simp
      · have : (w0.val ≤ i ∧ i < w.val) ↔ (w0.val ≤ i ∧ i < w.val + 1) := by omega
        simp only [this]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : y.val.length ≤ w.val := by simpa using hlt
    refine ⟨hl, fun i => ?_⟩
    rw [hy i]
    by_cases hi : i < y.val.length
    · have : (w0.val ≤ i ∧ i < w.val) ↔ w0.val ≤ i := by omega
      simp only [this]
    · have h1 : vw.val[i]? = none := List.getElem?_eq_none (by omega)
      simp only [h1, Option.map_none, ite_self]



/-! ### The reform loop -/

/-- A reforming patch whose deadline the clock has reached. -/
def ExpiredP (clock : Std.U64) (p : shatter.Patch) : Prop :=
  ∃ u : Std.U64, p.stage = shatter.Stage.Reforming u ∧ u.val ≤ clock.val

open Classical in
/-- The patch after the reform step: an expired one becomes idle. -/
noncomputable def reformP (clock : Std.U64) (p : shatter.Patch) : shatter.Patch :=
  if ExpiredP clock p then { p with stage := shatter.Stage.Idle } else p

open Classical in
/-- The walker after the first `k` patches were processed by the reform step. -/
noncomputable def reformW (clock : Std.U64) (ps : List shatter.Patch) :
    Nat → walker.Walker → walker.Walker
  | 0, o => o
  | k + 1, o =>
    match ps[k]? with
    | some p => if ExpiredP clock p then stateIf p walker.WalkerState.Ready (reformW clock ps k o)
        else reformW clock ps k o
    | none => reformW clock ps k o

theorem stateIf_cell (p : shatter.Patch) (s : walker.WalkerState) (o : walker.Walker) :
    (stateIf p s o).cell = o.cell := by
  unfold stateIf; split <;> rfl

theorem reformW_cell (clock : Std.U64) (ps : List shatter.Patch) (k : Nat) (o : walker.Walker) :
    (reformW clock ps k o).cell = o.cell := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold reformW
    cases ps[k]? with
    | none => exact ih
    | some p =>
      simp only
      split
      · rw [stateIf_cell, ih]
      · exact ih

/-- What the reform step looks like after the first `p` patches. -/
def ReformLists (clock : Std.U64) (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Nat) : Prop :=
  p ≤ x.patches.val.length ∧
    cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
    (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
      cp.val[q]? = some (if q < p then reformP clock pq else pq)) ∧
    (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
      cw.val[i]? = some (reformW clock x.patches.val p o))

def ReformInv (clock : Std.U64) (x s : scene.Scene) (p : Nat) : Prop :=
  ∃ cw cp, s = { x with walkers := cw, patches := cp } ∧ ReformLists clock x cw cp p

theorem reformLists_skip (clock : Std.U64) (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Nat) (pq : shatter.Patch)
    (hl : ReformLists clock x cw cp p) (hpm : p < x.patches.val.length)
    (hpq : x.patches.val[p]? = some pq) (hn : ¬ ExpiredP clock pq) :
    ReformLists clock x cw cp (p + 1) := by
  obtain ⟨hp, hcwl, hcpl, hcp, hcw⟩ := hl
  refine ⟨by omega, hcwl, hcpl, fun q hq => ?_, fun i hi => ?_⟩
  · obtain ⟨pq', h1, h2⟩ := hcp q hq
    refine ⟨pq', h1, ?_⟩
    rw [h2]
    by_cases hqp : q = p
    · subst hqp
      rw [hpq] at h1; cases h1
      simp [reformP, hn]
    · have : (q < p + 1) ↔ (q < p) := by omega
      simp only [this]
  · obtain ⟨o, ho, hco⟩ := hcw i hi
    refine ⟨o, ho, ?_⟩
    rw [hco]
    simp only [reformW, hpq, hn, ↓reduceIte]

open Classical in
theorem reformLists_expire (clock : Std.U64) (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Std.Usize) (pq : shatter.Patch)
    (hl : ReformLists clock x cw cp p.val) (hpm : p.val < x.patches.val.length)
    (hpq : x.patches.val[p.val]? = some pq) (hd : ExpiredP clock pq)
    (cw' : alloc.vec.Vec walker.Walker)
    (hcw' : cw'.val.length = cw.val.length ∧ ∀ i : Nat, cw'.val[i]? =
      (cw.val[i]?).map (stateIf pq walker.WalkerState.Ready)) :
    ReformLists clock x cw' (cp.set p { pq with stage := shatter.Stage.Idle }) (p.val + 1) := by
  obtain ⟨hp, hcwl, hcpl, hcp, hcw⟩ := hl
  refine ⟨by omega, by rw [hcw'.1, hcwl], by simp [alloc.vec.Vec.set_val_eq, hcpl], fun q hq => ?_,
    fun i hi => ?_⟩
  · obtain ⟨pq', h1, h2⟩ := hcp q hq
    refine ⟨pq', h1, ?_⟩
    simp only [alloc.vec.Vec.set_val_eq]
    by_cases hqp : q = p.val
    · subst hqp
      rw [h1] at hpq; cases hpq
      rw [List.getElem?_set_self (by omega)]
      simp [reformP, hd]
    · rw [List.getElem?_set_ne (Ne.symm hqp), h2]
      have : (q < p.val + 1) ↔ (q < p.val) := by omega
      simp only [this]
  · obtain ⟨o, ho, hco⟩ := hcw i hi
    refine ⟨o, ho, ?_⟩
    rw [hcw'.2 i, hco]
    simp only [Option.map_some, reformW, hpq, hd, ↓reduceIte]

theorem tick_loop1_body_spec (clock : Std.U64) (x : scene.Scene) (s : scene.Scene) (p : Std.Usize)
    (hinv : ReformInv clock x s p.val) :
    scene.Scene.tick_loop1.body clock s p ⦃ r =>
      match r with
      | .cont st => ReformInv clock x st.1 st.2.val ∧
          x.patches.val.length - st.2.val < x.patches.val.length - p.val
      | .done y => ∃ cw cp, y = sceneFields { x with walkers := cw, patches := cp } ∧
          ReformLists clock x cw cp x.patches.val.length ⦄ := by
  classical
  obtain ⟨cw, cp, rfl, hlists⟩ := hinv
  have hlists0 := hlists
  obtain ⟨hp, hcwl, hcpl, hcp, hcwf⟩ := hlists
  unfold scene.Scene.tick_loop1.body
  by_cases hlt : p < alloc.vec.Vec.len ({ x with walkers := cw, patches := cp } : scene.Scene).patches
  · simp only [hlt, ↓reduceIte]
    have hl : p.val < cp.val.length := hlt
    have hpm : p.val < x.patches.val.length := by omega
    obtain ⟨pq, hpq, hcpq⟩ := hcp p.val hpm
    simp only [lt_irrefl, ↓reduceIte] at hcpq
    simp only [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec cp p hl)
    intro p1 hp1
    have hp1e : p1 = pq := by
      rw [List.getElem?_eq_getElem hl] at hcpq
      rw [hp1]; exact Option.some.inj hcpq
    subst hp1e
    have hskip : ¬ ExpiredP clock p1 → ∀ (p2 : Std.Usize), p2.val = p.val + 1 →
        ReformInv clock x { x with walkers := cw, patches := cp } p2.val ∧
          x.patches.val.length - p2.val < x.patches.val.length - p.val := by
      intro hn p2 hp2
      refine ⟨⟨cw, cp, rfl, ?_⟩, by omega⟩
      rw [hp2]
      exact reformLists_skip clock x cw cp p.val p1 hlists0 hpm hpq hn
    cases hst : p1.stage with
    | Reforming u =>
      by_cases hge : clock ≥ u
      · have hgev : u.val ≤ clock.val := by simpa using hge
        have hex : ExpiredP clock p1 := ⟨u, hst, hgev⟩
        simp only [hge, ↓reduceIte]
        apply spec_bind (tick_sweep_spec cw cp p p1 hcpq 0#usize)
        intro v hv
        simp only [alloc.vec.Vec.index_mut_slice_index]
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec cp p hl)
        rintro ⟨p2, back⟩ ⟨hp2, hback⟩
        apply spec_bind (Usize.add_spec (x := p) (y := 1#usize) (by scalar_tac))
        intro p3 hp3
        have hp3v : p3.val = p.val + 1 := by simpa using hp3
        have hp2e : p2 = p1 := by
          rw [List.getElem?_eq_getElem hl] at hcpq
          rw [hp2]; exact Option.some.inj hcpq
        subst hp2e
        subst hback
        rw [spec_ok]
        dsimp only
        refine ⟨⟨v, _, rfl, ?_⟩, by omega⟩
        rw [hp3v]
        exact reformLists_expire clock x cw cp p p2 hlists0 hpm hpq hex v
          ⟨hv.1, fun i => by rw [hv.2 i]; simp⟩
      · have hn : ¬ ExpiredP clock p1 := by
          rintro ⟨u', hu', hle⟩
          rw [hst] at hu'; cases hu'
          exact hge (by simpa using hle)
        simp only [hge, ↓reduceIte]
        apply spec_bind (Usize.add_spec (x := p) (y := 1#usize) (by scalar_tac))
        intro p2 hp2
        rw [spec_ok]
        exact hskip hn p2 (by simpa using hp2)
    | _ =>
      all_goals
        have hn : ¬ ExpiredP clock p1 := by
          rintro ⟨u', hu', _⟩
          rw [hst] at hu'; cases hu'
        apply spec_bind (Usize.add_spec (x := p) (y := 1#usize) (by scalar_tac))
        intro p2 hp2
        rw [spec_ok]
        exact hskip hn p2 (by simpa using hp2)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : cp.val.length ≤ p.val := by simpa using hlt
    have hpe : p.val = x.patches.val.length := by omega
    refine ⟨cw, cp, rfl, ?_⟩
    rw [← hpe]; exact hlists0

/-- The reform loop of `tick`: every patch that is reforming with its deadline reached is idle, and
every walker standing in such a patch is ready. Nothing else changes. -/
theorem tick_loop1_spec (clock : Std.U64) (x : scene.Scene) :
    scene.Scene.tick_loop1 x clock 0#usize ⦃ y =>
      ∃ cw cp, y = sceneFields { x with walkers := cw, patches := cp } ∧
        cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
        (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
          cp.val[q]? = some (reformP clock pq)) ∧
        (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
          cw.val[i]? = some (reformW clock x.patches.val x.patches.val.length o)) ⦄ := by
  unfold scene.Scene.tick_loop1
  refine loop.spec_decr_nat (fun st : scene.Scene × Std.Usize => x.patches.val.length - st.2.val)
    (fun st => ReformInv clock x st.1 st.2.val) _ _ _ ?_ ?_
  · rintro ⟨s, p⟩ hinv
    refine spec_mono (tick_loop1_body_spec clock x s p hinv) ?_
    intro r hr
    cases r with
    | cont st => exact hr
    | done y =>
      obtain ⟨cw, cp, hy, hp, h1, h2, h3, h4⟩ := hr
      refine ⟨cw, cp, hy, h1, h2, fun q hq => ?_, h4⟩
      obtain ⟨pq, hpq, hc⟩ := h3 q hq
      exact ⟨pq, hpq, by simpa [hq] using hc⟩
  · refine ⟨x.walkers, x.patches, rfl, by simp, rfl, rfl, fun q hq => ?_, fun i hi => ?_⟩
    · obtain ⟨pq, hpq⟩ : ∃ pq, x.patches.val[q]? = some pq := ⟨_, List.getElem?_eq_getElem hq⟩
      exact ⟨pq, hpq, by simp [hpq]⟩
    · obtain ⟨o, ho⟩ : ∃ o, x.walkers.val[i]? = some o := ⟨_, List.getElem?_eq_getElem hi⟩
      exact ⟨o, ho, by simp [ho, reformW]⟩

/-! ### `tick`'s active path, exactly and in total -/

theorem reformW_eq_or (clock : Std.U64) (ps : List shatter.Patch) (k : Nat) (o : walker.Walker) :
    reformW clock ps k o = o ∨ ∀ c, (reformW clock ps k o).state ≠ walker.WalkerState.Crossing c := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    unfold reformW
    cases hps : ps[k]? with
    | none => exact ih
    | some p =>
      simp only
      split
      · by_cases hh : PatchHas p (reformW clock ps k o).cell.val
        · right
          intro c
          simp [stateIf, hh]
        · simp only [stateIf, hh, ↓reduceIte]
          exact ih
      · exact ih

theorem drainW_eq_or (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (o : walker.Walker) :
    drainW ws ps k o = o ∨ ∀ c, (drainW ws ps k o).state ≠ walker.WalkerState.Crossing c := by
  unfold drainW
  split
  · right; intro c; simp [parkedWalker]
  · left; rfl

/-- `tick` on its active path, in total under the reservation invariant: the walkers cross as far as
their time allows; draining patches park; reforming patches whose deadline is reached become idle with
their walkers ready. The step keeps the reservation invariant, and nothing else changes. -/
theorem tick_active_spec (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max) (hinv : ResInv self) :
    scene.Scene.tick self stamp wall ⦃ res =>
      ∃ (v z : Std.U64) (hold : alloc.vec.Vec Std.Usize) (walk cw : alloc.vec.Vec walker.Walker)
        (cp : alloc.vec.Vec shatter.Patch),
        v.val = self.stamp.revision.val + 1 ∧ z.val = self.clock.val + (wall.val - self.wall.val) ∧
        ResInvL walk.val hold.val ∧ walk.val.length = self.walkers.val.length ∧
        hold.val.length = self.holds.val.length ∧
        ResInvL cw.val hold.val ∧
        cp.val.length = self.patches.val.length ∧
        (∀ q, q < self.patches.val.length → ∃ pq, self.patches.val[q]? = some pq ∧
          cp.val[q]? = some (reformP z (drainP walk.val pq))) ∧
        cw.val.length = walk.val.length ∧
        (∀ i, i < walk.val.length → ∃ o, walk.val[i]? = some o ∧
          cw.val[i]? = some (reformW z (self.patches.val.map (drainP walk.val)) self.patches.val.length
            (drainW walk.val self.patches.val self.patches.val.length o))) ∧
        res = (.Ok (bumped self v),
          { self with holds := hold, walkers := cw, patches := cp, stamp := bumped self v,
                      clock := z, wall := wall }) ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  rw [he]
  have hnw : ¬ wall < self.wall := by simpa using hw
  have hsub := Std.U64.sub_spec (x := wall) (y := self.wall) (by scalar_tac)
  obtain ⟨d, hd, hdv⟩ := spec_eq_ok hsub
  simp [core.result.Result.Insts.CoreOpsTry.branch, hnw, hs, hi, hp, hr,
    core.option.Option.is_some, hd]
  rcases u64_checked_add self.clock d with ⟨hle, z, hz, hzv⟩ | ⟨hgt, hn⟩
  · simp only [lift, hz, Std.bind_ok, core.option.Option.ok_or]
    apply spec_bind (tick_loop0_spec d self.holds self.walkers 0#usize (by simp) hinv)
    rintro ⟨hold, walk⟩ ⟨hinv1, hl1, hl2⟩
    apply spec_bind (drain_patches_spec _ (fun wk hwk c hc => (hinv1.1 wk hwk c hc).2.2))
    rintro self1 ⟨cwd, cpd, rfl, hlw, hlp, hdp, hdw⟩
    apply spec_bind (tick_loop1_spec z _)
    rintro ⟨l, t, w, v2, v3, v4, v5, v6, v7, v8, s, i, i1, b1, b2, b3, i2, o1, i3⟩
      ⟨cw, cp, hy, hlw2, hlp2, hdp2, hdw2⟩
    simp only [sceneFields, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩ := hy
    refine (spec_ok _).mpr ?_
    dsimp only at hlw hlp hdp hdw hlw2 hlp2 hdp2 hdw2 hinv1 hl1 hl2
    have hcpd : cpd.val = self.patches.val.map (drainP walk.val) := by
      apply List.ext_getElem?
      intro q
      by_cases hq : q < self.patches.val.length
      · obtain ⟨pq, hpq, hc⟩ := hdp q hq
        rw [hc, List.getElem?_map, hpq]; rfl
      · have h1 : cpd.val[q]? = none := List.getElem?_eq_none (by omega)
        have h2 : (self.patches.val.map (drainP walk.val))[q]? = none :=
          List.getElem?_eq_none (by simp; omega)
        rw [h1, h2]
    refine ⟨v, hv, i, by omega, v6, walk, hinv1, hl1, hl2, v7, ?_, v8, by omega, ?_, by omega, ?_, ?_⟩
    · have hrel : ∀ j, j < walk.val.length → ∃ o n, walk.val[j]? = some o ∧ v7.val[j]? = some n ∧
          (n = o ∨ ∀ c, n.state ≠ walker.WalkerState.Crossing c) := by
        intro j hj
        obtain ⟨o', ho', hco'⟩ := hdw j hj
        obtain ⟨o'', ho'', hco''⟩ := hdw2 j (by omega)
        rw [hco'] at ho''; cases ho''
        refine ⟨o', _, ho', hco'', ?_⟩
        rcases reformW_eq_or i cpd.val cpd.val.length
          (drainW walk.val self.patches.val self.patches.val.length o') with h | h
        · rcases drainW_eq_or walk.val self.patches.val self.patches.val.length o' with h' | h'
          · left; rw [h]; exact h'
          · right; rw [h]; exact h'
        · right; exact h
      exact resInvL_relaxed walk.val v7.val v6.val hinv1 (by omega) hrel
    · intro q hq
      obtain ⟨pq, hpq, hc⟩ := hdp q hq
      obtain ⟨pq', hpq', hc'⟩ := hdp2 q (by omega)
      rw [hc] at hpq'; cases hpq'
      exact ⟨pq, hpq, hc'⟩
    · intro j hj
      obtain ⟨o', ho', hco'⟩ := hdw j hj
      obtain ⟨o'', ho'', hco''⟩ := hdw2 j (by omega)
      rw [hco'] at ho''; cases ho''
      refine ⟨o', ho', ?_⟩
      rw [hco'', hcpd, List.length_map]
    · simp only [bumped]
  · omega

end Labyrinth
