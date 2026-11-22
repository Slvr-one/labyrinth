module
public import LabyrinthCore.SceneReservation
public import LabyrinthCore.SceneEditPublish

/-! Shatter (S6), part 1: `Scene::drain_patches`. A patch in stage `Draining` becomes `Parked` once no
crossing walker has its source or target in the patch; every walker standing in a newly parked
patch (and not crossing) becomes `Parked` with it. Crossing walkers are never touched, so the set
of crossing walkers is the same before and after, and whether a patch drains depends on that set
only. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- A crossing walker with its source or target in the patch. -/
def Touches (ws : List walker.Walker) (p : shatter.Patch) : Prop :=
  ∃ wk ∈ ws, ∃ c, wk.state = walker.WalkerState.Crossing c ∧
    (PatchHas p c.source.val ∨ PatchHas p c.target.val)

/-- The walker is mid-crossing. -/
def IsCrossing (wk : walker.Walker) : Prop := ∃ c, wk.state = walker.WalkerState.Crossing c

/-- The scan of `drain_patches` for patch `p`: some crossing walker from `w0` on touches it. -/
theorem drain_scan_spec (v : alloc.vec.Vec walker.Walker) (v1 : alloc.vec.Vec shatter.Patch)
    (p : Std.Usize) (pp : shatter.Patch) (hp : v1.val[p.val]? = some pp)
    (cr0 : Bool) (w0 : Std.Usize) :
    scene.Scene.drain_patches_loop0_loop0 v v1 p cr0 w0 ⦃ r =>
      (r = true ↔ cr0 = true ∨ ∃ j, w0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧
        (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)) ⦄ := by
  unfold scene.Scene.drain_patches_loop0_loop0
  refine loop.spec_decr_nat (fun x : Bool × Std.Usize => v.length - x.2.val)
    (fun x : Bool × Std.Usize =>
      (x.1 = true ∨ ∃ j, x.2.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧
        (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)) ↔
      (cr0 = true ∨ ∃ j, w0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧
        (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)))
    (fun r : Bool => (r = true ↔ cr0 = true ∨ ∃ j, w0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
      wk.state = walker.WalkerState.Crossing c ∧
      (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)))
    _ _ ?_ Iff.rfl
  rintro ⟨cr, w⟩ hinv
  simp only at hinv
  unfold scene.Scene.drain_patches_loop0_loop0.body
  by_cases hlt : w < alloc.vec.Vec.len v
  · simp only [hlt, ↓reduceIte]
    have hl : w.val < v.val.length := hlt
    have hvl : v.length = v.val.length := rfl
    simp only [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec v w hl)
    intro wk hwk
    have hwks : v.val[w.val]? = some wk := by
      rw [List.getElem?_eq_getElem hl, hwk]
    have hm : ∀ st : walker.WalkerState, (match st with
        | walker.WalkerState.Ready => (ok cr : Result Bool)
        | walker.WalkerState.Crossing active => do
          let p1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice shatter.Patch) v1 p
          let b ← shatter.Patch.contains p1 active.source
          if b = true then ok true
          else do
            let b1 ← shatter.Patch.contains p1 active.target
            if b1 = true then ok true else ok cr
        | walker.WalkerState.Parked => ok cr
        | walker.WalkerState.Hidden => ok cr
        | walker.WalkerState.Terminated => ok cr) ⦃ r =>
          (r = true ↔ cr = true ∨ ∃ c, st = walker.WalkerState.Crossing c ∧
            (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)) ⦄ := by
      intro st
      cases st with
      | Crossing c =>
        simp only [alloc.vec.Vec.index_slice_index]
        have hpl : p.val < v1.val.length := (List.getElem?_eq_some_iff.mp hp).1
        apply spec_bind (alloc.vec.Vec.index_usize_spec v1 p hpl)
        intro p1 hp1
        have hp1e : p1 = pp := by
          rw [List.getElem?_eq_getElem hpl] at hp
          rw [hp1]; exact Option.some.inj hp
        subst hp1e
        apply spec_bind (patch_contains_spec p1 c.source)
        intro b hb
        by_cases hbt : b = true
        · simp only [hbt, ↓reduceIte, spec_ok]
          constructor
          · intro _; exact Or.inr ⟨c, rfl, Or.inl (hb.mp hbt)⟩
          · intro _; trivial
        · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
          apply spec_bind (patch_contains_spec p1 c.target)
          intro b1 hb1
          by_cases hb1t : b1 = true
          · simp only [hb1t, ↓reduceIte, spec_ok]
            constructor
            · intro _; exact Or.inr ⟨c, rfl, Or.inr (hb1.mp hb1t)⟩
            · intro _; trivial
          · simp only [hb1t, Bool.false_eq_true, ↓reduceIte, spec_ok]
            constructor
            · intro h; exact Or.inl h
            · rintro (h | ⟨c', hc', h'⟩)
              · exact h
              · cases hc'
                rcases h' with h' | h'
                · exact absurd (hb.mpr h') hbt
                · exact absurd (hb1.mpr h') hb1t
      | Ready => rw [spec_ok]; simp
      | Parked => rw [spec_ok]; simp
      | Hidden => rw [spec_ok]; simp
      | Terminated => rw [spec_ok]; simp
    apply spec_bind (hm wk.state)
    intro cr1 hcr1
    apply spec_bind (usize_succ_spec w (by have := v.property; scalar_tac))
    intro w2 hw2
    rw [spec_ok]
    have hw2v : w2.val = w.val + 1 := hw2
    refine ⟨?_, by show v.length - w2.val < v.length - w.val; omega⟩
    simp only [hw2v]
    rw [← hinv]
    simp only [hcr1]
    constructor
    · rintro ((h | ⟨c, hc, hm'⟩) | ⟨j, hj, wk', c, hq, hs', hm'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w.val, le_refl _, wk, c, hwks, hc, hm'⟩
      · exact Or.inr ⟨j, by omega, wk', c, hq, hs', hm'⟩
    · rintro (h | ⟨j, hj, wk', c, hq, hs', hm'⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hji : j = w.val
        · subst hji
          rw [hwks] at hq
          cases hq
          exact Or.inl (Or.inr ⟨c, hs', hm'⟩)
        · exact Or.inr ⟨j, by omega, wk', c, hq, hs', hm'⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hl : ¬ w.val < v.val.length := hlt
    rw [← hinv]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, hj, wk, c, hq, _⟩)
      · exact h
      · exfalso
        have := (List.getElem?_eq_some_iff.mp hq).1
        omega

/-- The walker after being parked with its patch. -/
def parkedWalker (o : walker.Walker) : walker.Walker := { o with state := walker.WalkerState.Parked }

open Classical in
/-- The park loop: from index `w0` on, every walker whose cell the patch covers becomes `Parked`. -/
theorem drain_park_spec (v1 : alloc.vec.Vec shatter.Patch) (p : Std.Usize) (pp : shatter.Patch)
    (hp : v1.val[p.val]? = some pp) (ws : alloc.vec.Vec walker.Walker) :
    ∀ (x : alloc.vec.Vec walker.Walker) (w : Std.Usize), w.val ≤ ws.val.length →
      x.val.length = ws.val.length →
      (∀ i, i < ws.val.length → ∃ o, ws.val[i]? = some o ∧
        x.val[i]? = some (if i < w.val ∧ PatchHas pp o.cell.val then parkedWalker o else o)) →
      scene.Scene.drain_patches_loop0_loop1 x v1 p w ⦃ r =>
        r.val.length = ws.val.length ∧
        ∀ i, i < ws.val.length → ∃ o, ws.val[i]? = some o ∧
          r.val[i]? = some (if PatchHas pp o.cell.val then parkedWalker o else o) ⦄ := by
  intro x w hw hlen hx
  unfold scene.Scene.drain_patches_loop0_loop1
  refine loop.spec_decr_nat (fun s : alloc.vec.Vec walker.Walker × Std.Usize =>
      ws.val.length - s.2.val)
    (fun s => s.2.val ≤ ws.val.length ∧ s.1.val.length = ws.val.length ∧
      ∀ i, i < ws.val.length → ∃ o, ws.val[i]? = some o ∧
        s.1.val[i]? = some (if i < s.2.val ∧ PatchHas pp o.cell.val then parkedWalker o else o))
    (fun r : alloc.vec.Vec walker.Walker => r.val.length = ws.val.length ∧
        ∀ i, i < ws.val.length → ∃ o, ws.val[i]? = some o ∧
          r.val[i]? = some (if PatchHas pp o.cell.val then parkedWalker o else o))
    _ _ ?_ ⟨hw, hlen, hx⟩
  rintro ⟨y, w⟩ ⟨hw, hlen, hy⟩
  simp only at hw hlen hy
  unfold scene.Scene.drain_patches_loop0_loop1.body
  by_cases hlt : w < alloc.vec.Vec.len y
  · simp only [hlt, ↓reduceIte]
    have hl : w.val < y.val.length := hlt
    have hwl : w.val < ws.val.length := by omega
    have hpl : p.val < v1.val.length := (List.getElem?_eq_some_iff.mp hp).1
    simp only [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec v1 p hpl)
    intro p1 hp1
    have hp1e : p1 = pp := by
      rw [List.getElem?_eq_getElem hpl] at hp
      rw [hp1]; exact Option.some.inj hp
    subst hp1e
    apply spec_bind (alloc.vec.Vec.index_usize_spec y w hl)
    intro w1 hw1
    obtain ⟨o, hos, hyo⟩ := hy w.val hwl
    have hw1o : w1 = o := by
      rw [List.getElem?_eq_getElem hl] at hyo
      simp only [lt_irrefl, false_and, ↓reduceIte, Option.some.injEq] at hyo
      rw [hw1]; exact hyo
    subst hw1o
    apply spec_bind (patch_contains_spec p1 w1.cell)
    intro b hb
    have hstep : ∀ z : alloc.vec.Vec walker.Walker,
        (z = if b = true then y.set w (parkedWalker w1) else y) →
        ∀ w2 : Std.Usize, w2.val = w.val + 1 →
        (w2.val ≤ ws.val.length ∧ z.val.length = ws.val.length ∧
          ∀ i, i < ws.val.length → ∃ o, ws.val[i]? = some o ∧
            z.val[i]? = some (if i < w2.val ∧ PatchHas p1 o.cell.val then parkedWalker o else o)) := by
      intro z hz w2 hw2
      subst hz
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte]
        refine ⟨by omega, by simp [alloc.vec.Vec.set_val_eq, hlen], fun i hi => ?_⟩
        by_cases hiw : i = w.val
        · subst hiw
          refine ⟨w1, hos, ?_⟩
          have hh := hb.mp hbt
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_self hl]
          simp [hw2, hh]
        · obtain ⟨o', ho', hyo'⟩ := hy i hi
          refine ⟨o', ho', ?_⟩
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_ne (Ne.symm hiw), hyo']
          have : (i < w.val) ↔ (i < w2.val) := by omega
          simp only [this]
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, hlen, fun i hi => ?_⟩
        obtain ⟨o', ho', hyo'⟩ := hy i hi
        refine ⟨o', ho', ?_⟩
        rw [hyo']
        by_cases hiw : i = w.val
        · subst hiw
          rw [hos] at ho'
          cases ho'
          have hh : ¬ PatchHas p1 w1.cell.val := fun h => hbt (hb.mpr h)
          simp [hh]
        · have : (i < w.val) ↔ (i < w2.val) := by omega
          simp only [this]
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte]
      simp only [alloc.vec.Vec.index_mut_slice_index, Aeneas.Std.bind_assoc]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec y w hl)
      rintro ⟨w2, back⟩ ⟨hw2', hback⟩
      have hw2e : w2 = w1 := by rw [hw2', hw1]
      subst hw2e
      apply spec_bind (m := (ok (back (parkedWalker w2)) : Result (alloc.vec.Vec walker.Walker)))
        (show (ok (back (parkedWalker w2)) : Result (alloc.vec.Vec walker.Walker)) ⦃ fun v =>
          v = back (parkedWalker w2) ⦄ by rw [spec_ok])
      intro v2 hv2
      apply spec_bind (usize_succ_spec w (by have := ws.property; scalar_tac))
      intro w3 hw3
      rw [spec_ok]
      have hh := hstep v2 (by rw [hv2, hback]; simp [hbt]) w3 hw3
      refine ⟨hh, by show ws.val.length - w3.val < ws.val.length - w.val; omega⟩
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte, bind_ok]
      apply spec_bind (usize_succ_spec w (by have := ws.property; scalar_tac))
      intro w3 hw3
      rw [spec_ok]
      have hh := hstep y (by simp [hbt]) w3 hw3
      refine ⟨hh, by show ws.val.length - w3.val < ws.val.length - w.val; omega⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hl : ¬ w.val < y.val.length := hlt
    refine ⟨hlen, fun i hi => ?_⟩
    obtain ⟨o, ho, hyo⟩ := hy i hi
    refine ⟨o, ho, ?_⟩
    rw [hyo]
    have : i < w.val := by omega
    simp only [this, true_and]

/-! ### The whole of `drain_patches` -/

/-- Every crossing walker stands in its source cell (true from `begin_crossing` until the crossing
ends). -/
def CrossAtSource (ws : List walker.Walker) : Prop :=
  ∀ wk ∈ ws, ∀ c, wk.state = walker.WalkerState.Crossing c → wk.cell = c.source

/-- A patch that `drain_patches` parks: draining, with no crossing walker touching it. -/
def Drains (ws : List walker.Walker) (p : shatter.Patch) : Prop :=
  p.stage = shatter.Stage.Draining ∧ ¬ Touches ws p

open Classical in
/-- The patch after one `drain_patches`. -/
noncomputable def drainP (ws : List walker.Walker) (p : shatter.Patch) : shatter.Patch :=
  if Drains ws p then { p with stage := shatter.Stage.Parked } else p

open Classical in
/-- The walker after the first `k` patches were processed. -/
noncomputable def drainW (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (o : walker.Walker) : walker.Walker :=
  if ∃ q, q < k ∧ ∃ pq, ps[q]? = some pq ∧ Drains ws pq ∧ PatchHas pq o.cell.val
  then parkedWalker o else o

theorem parkedWalker_cell (o : walker.Walker) : (parkedWalker o).cell = o.cell := rfl

theorem drainW_cell (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (o : walker.Walker) : (drainW ws ps k o).cell = o.cell := by
  unfold drainW; split <;> rfl

theorem patchHas_parked (pq : shatter.Patch) (cell : Nat) (h : pq.stage = shatter.Stage.Draining) :
    PatchHas { pq with stage := shatter.Stage.Parked } cell ↔ PatchHas pq cell := by
  simp [PatchHas, h]

/-- Under `CrossAtSource`, parking never touches a crossing walker, so a patch's `Touches` verdict
does not change while earlier patches drain. -/
theorem touches_drainW (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (hcs : CrossAtSource ws) (cw : List walker.Walker)
    (hcw : ∀ i, i < ws.length → ∃ o, ws[i]? = some o ∧ cw[i]? = some (drainW ws ps k o))
    (hlen : cw.length = ws.length) (pp : shatter.Patch) (hk : ∀ q, q < k → ∀ pq, ps[q]? = some pq →
      Drains ws pq → ¬ Touches ws pq) :
    Touches cw pp ↔ Touches ws pp := by
  have hcross : ∀ i, i < ws.length → ∀ o, ws[i]? = some o → ∀ n, cw[i]? = some n →
      (IsCrossing n ↔ IsCrossing o) ∧ (IsCrossing o → n = o) := by
    intro i hi o ho n hn
    obtain ⟨o', ho', hn'⟩ := hcw i hi
    rw [ho] at ho'; cases ho'
    rw [hn] at hn'; cases hn'
    unfold drainW
    by_cases hex : ∃ q, q < k ∧ ∃ pq, ps[q]? = some pq ∧ Drains ws pq ∧ PatchHas pq o.cell.val
    · simp only [hex, ↓reduceIte]
      constructor
      · constructor
        · rintro ⟨c, hc⟩; simp [parkedWalker] at hc
        · rintro ⟨c, hc⟩
          exfalso
          obtain ⟨q, hq, pq, hpq, hd, hh⟩ := hex
          have hcell := hcs o (List.mem_of_getElem? ho) c hc
          apply hk q hq pq hpq hd
          exact ⟨o, List.mem_of_getElem? ho, c, hc, Or.inl (by rw [← hcell]; exact hh)⟩
      · rintro ⟨c, hc⟩
        exfalso
        obtain ⟨q, hq, pq, hpq, hd, hh⟩ := hex
        have hcell := hcs o (List.mem_of_getElem? ho) c hc
        apply hk q hq pq hpq hd
        exact ⟨o, List.mem_of_getElem? ho, c, hc, Or.inl (by rw [← hcell]; exact hh)⟩
    · simp only [hex, ↓reduceIte]
      exact ⟨trivial, fun _ => trivial⟩
  constructor
  · rintro ⟨n, hn, c, hc, hs⟩
    obtain ⟨i, hi, hni⟩ := List.getElem_of_mem hn
    have hiw : i < ws.length := by omega
    obtain ⟨o, ho, _⟩ := hcw i hiw
    have hn? : cw[i]? = some n := by rw [List.getElem?_eq_getElem hi, hni]
    obtain ⟨hiff, hsame⟩ := hcross i hiw o ho n hn?
    have hcr : IsCrossing o := hiff.mp ⟨c, hc⟩
    have := hsame hcr
    subst this
    exact ⟨n, List.mem_of_getElem? ho, c, hc, hs⟩
  · rintro ⟨o, ho, c, hc, hs⟩
    obtain ⟨i, hi, hoi⟩ := List.getElem_of_mem ho
    have ho? : ws[i]? = some o := by rw [List.getElem?_eq_getElem hi, hoi]
    obtain ⟨o', ho', hn'⟩ := hcw i hi
    rw [ho?] at ho'; cases ho'
    obtain ⟨hiff, hsame⟩ := hcross i hi o ho? _ hn'
    have := hsame ⟨c, hc⟩
    exact ⟨_, List.mem_of_getElem? hn', c, by rw [this]; exact hc, hs⟩

theorem stage_eq_spec (a b : shatter.Stage) :
    shatter.Stage.Insts.CoreCmpPartialEqStage.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold shatter.Stage.Insts.CoreCmpPartialEqStage.eq
  cases a <;> cases b <;>
    simp [shatter.Stage.read_discriminant, core.cmp.impls.PartialEqU64.eq, spec_ok]
  all_goals (simp only [lift, spec_ok]; simp)

/-- Reading the touched verdict off the scan. -/
theorem touches_iff_scan (ws : List walker.Walker) (pp : shatter.Patch) :
    (∃ j, 0 ≤ j ∧ ∃ wk c, ws[j]? = some wk ∧ wk.state = walker.WalkerState.Crossing c ∧
      (PatchHas pp c.source.val ∨ PatchHas pp c.target.val)) ↔ Touches ws pp := by
  constructor
  · rintro ⟨j, _, wk, c, hq, hs, hm⟩
    exact ⟨wk, List.mem_of_getElem? hq, c, hs, hm⟩
  · rintro ⟨wk, hmem, c, hs, hm⟩
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
    exact ⟨j, Nat.zero_le _, wk, c, by rw [List.getElem?_eq_getElem hj, hjw], hs, hm⟩

/-- What the walker and patch lists look like after the first `p` patches were processed. -/
def DrainLists (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Nat) : Prop :=
  p ≤ x.patches.val.length ∧
    cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
    (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
      cp.val[q]? = some (if q < p then drainP x.walkers.val pq else pq)) ∧
    (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
      cw.val[i]? = some (drainW x.walkers.val x.patches.val p o))

/-- The scene `drain_patches` is in after processing the first `p` patches. -/
def DrainInv (x : scene.Scene) (s : scene.Scene) (p : Nat) : Prop :=
  ∃ cw cp, s = { x with walkers := cw, patches := cp } ∧ DrainLists x cw cp p

theorem drainW_succ_iff (ws : List walker.Walker) (ps : List shatter.Patch) (p : Nat)
    (pq : shatter.Patch) (hpq : ps[p]? = some pq) (o : walker.Walker) :
    (∃ q, q < p + 1 ∧ ∃ pq', ps[q]? = some pq' ∧ Drains ws pq' ∧ PatchHas pq' o.cell.val) ↔
      ((∃ q, q < p ∧ ∃ pq', ps[q]? = some pq' ∧ Drains ws pq' ∧ PatchHas pq' o.cell.val) ∨
        (Drains ws pq ∧ PatchHas pq o.cell.val)) := by
  constructor
  · rintro ⟨q, hq, pq', h1, h2, h3⟩
    by_cases hqp : q = p
    · subst hqp; rw [hpq] at h1; cases h1; exact Or.inr ⟨h2, h3⟩
    · exact Or.inl ⟨q, by omega, pq', h1, h2, h3⟩
  · rintro (⟨q, hq, h⟩ | ⟨h2, h3⟩)
    · exact ⟨q, by omega, h⟩
    · exact ⟨p, by omega, pq, hpq, h2, h3⟩

theorem drainW_succ_skip (ws : List walker.Walker) (ps : List shatter.Patch) (p : Nat)
    (pq : shatter.Patch) (hpq : ps[p]? = some pq) (o : walker.Walker)
    (hn : ¬ (Drains ws pq ∧ PatchHas pq o.cell.val)) : drainW ws ps (p + 1) o = drainW ws ps p o := by
  have hi := drainW_succ_iff ws ps p pq hpq o
  unfold drainW
  by_cases h : ∃ q, q < p + 1 ∧ ∃ pq', ps[q]? = some pq' ∧ Drains ws pq' ∧ PatchHas pq' o.cell.val
  · have h' := (hi.mp h).resolve_right hn
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ (∃ q, q < p ∧ ∃ pq', ps[q]? = some pq' ∧ Drains ws pq' ∧ PatchHas pq' o.cell.val) :=
      fun h2 => h (hi.mpr (Or.inl h2))
    simp only [h, h', ↓reduceIte]

theorem drainW_succ_hit (ws : List walker.Walker) (ps : List shatter.Patch) (p : Nat)
    (pq : shatter.Patch) (hpq : ps[p]? = some pq) (o : walker.Walker)
    (hd : Drains ws pq) (hh : PatchHas pq o.cell.val) : drainW ws ps (p + 1) o = parkedWalker o := by
  have hi := drainW_succ_iff ws ps p pq hpq o
  have h := hi.mpr (Or.inr ⟨hd, hh⟩)
  unfold drainW
  simp only [h, ↓reduceIte]

theorem parked_drainW (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (o : walker.Walker) : parkedWalker (drainW ws ps k o) = parkedWalker o := by
  unfold drainW; split <;> simp [parkedWalker]

/-- A patch that does not drain is skipped without changing either list. -/
theorem drainLists_skip (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Nat) (pq : shatter.Patch)
    (hl : DrainLists x cw cp p) (hpm : p < x.patches.val.length)
    (hpq : x.patches.val[p]? = some pq) (hn : ¬ Drains x.walkers.val pq) :
    DrainLists x cw cp (p + 1) := by
  obtain ⟨hp, hcwl, hcpl, hcp, hcw⟩ := hl
  refine ⟨by omega, hcwl, hcpl, fun q hq => ?_, fun i hi => ?_⟩
  · obtain ⟨pq', h1, h2⟩ := hcp q hq
    refine ⟨pq', h1, ?_⟩
    rw [h2]
    by_cases hqp : q = p
    · subst hqp
      rw [hpq] at h1; cases h1
      simp [drainP, hn]
    · have : (q < p + 1) ↔ (q < p) := by omega
      simp only [this]
  · obtain ⟨o, ho, hco⟩ := hcw i hi
    exact ⟨o, ho, by rw [hco, drainW_succ_skip _ _ p pq hpq o (fun h => hn h.1)]⟩

open Classical in
/-- A draining patch is parked and its walkers are parked with it. -/
theorem drainLists_park (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (p : Std.Usize) (pq : shatter.Patch)
    (hl : DrainLists x cw cp p.val) (hpm : p.val < x.patches.val.length)
    (hpq : x.patches.val[p.val]? = some pq) (hd : Drains x.walkers.val pq)
    (cw' : alloc.vec.Vec walker.Walker)
    (hcw' : cw'.val.length = cw.val.length ∧ ∀ i, i < cw.val.length → ∃ o, cw.val[i]? = some o ∧
      cw'.val[i]? = some (if PatchHas { pq with stage := shatter.Stage.Parked } o.cell.val
        then parkedWalker o else o)) :
    DrainLists x cw' (cp.set p { pq with stage := shatter.Stage.Parked }) (p.val + 1) := by
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
      simp [drainP, hd]
    · rw [List.getElem?_set_ne (Ne.symm hqp), h2]
      have : (q < p.val + 1) ↔ (q < p.val) := by omega
      simp only [this]
  · obtain ⟨o, ho, hco⟩ := hcw i hi
    obtain ⟨o', ho', hco'⟩ := hcw'.2 i (by omega)
    rw [hco] at ho'; cases ho'
    refine ⟨o, ho, ?_⟩
    rw [hco']
    have hh : PatchHas { pq with stage := shatter.Stage.Parked } o.cell.val ↔ PatchHas pq o.cell.val :=
      patchHas_parked pq _ hd.1
    have hcell := drainW_cell x.walkers.val x.patches.val p.val o
    simp only [hcell]
    by_cases hhas : PatchHas pq o.cell.val
    · rw [drainW_succ_hit _ _ p.val pq hpq o hd hhas]
      simp only [hh.mpr hhas, ↓reduceIte, parked_drainW]
    · rw [drainW_succ_skip _ _ p.val pq hpq o (fun h => hhas h.2)]
      simp only [hhas, hh, ↓reduceIte]

theorem drain_patches_body_spec (x : scene.Scene) (hcs : CrossAtSource x.walkers.val)
    (s : scene.Scene) (p : Std.Usize) (hinv : DrainInv x s p.val) :
    scene.Scene.drain_patches_loop0.body s p ⦃ r =>
      match r with
      | .cont st => DrainInv x st.1 st.2.val ∧
          x.patches.val.length - st.2.val < x.patches.val.length - p.val
      | .done y => ∃ cw cp, y = sceneFields { x with walkers := cw, patches := cp } ∧
          cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
          (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
            cp.val[q]? = some (drainP x.walkers.val pq)) ∧
          (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
            cw.val[i]? = some (drainW x.walkers.val x.patches.val x.patches.val.length o)) ⦄ := by
  obtain ⟨cw, cp, rfl, hlists⟩ := hinv
  obtain ⟨hp, hcwl, hcpl, hcp, hcwf⟩ := hlists
  unfold scene.Scene.drain_patches_loop0.body
  by_cases hlt : p < alloc.vec.Vec.len ({ x with walkers := cw, patches := cp } : scene.Scene).patches
  · simp only [hlt, ↓reduceIte]
    have hl : p.val < cp.val.length := hlt
    have hpm : p.val < x.patches.val.length := by omega
    obtain ⟨pq, hpq, hcpq⟩ := hcp p.val hpm
    simp only [lt_irrefl, ↓reduceIte] at hcpq
    have hlists : DrainLists x cw cp p.val := ⟨hp, hcwl, hcpl, hcp, hcwf⟩
    simp only [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec cp p hl)
    intro p1 hp1
    have hp1e : p1 = pq := by
      rw [List.getElem?_eq_getElem hl] at hcpq
      rw [hp1]; exact Option.some.inj hcpq
    subst hp1e
    apply spec_bind (stage_eq_spec p1.stage shatter.Stage.Draining)
    intro b hb
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte]
      apply spec_bind (drain_scan_spec cw cp p p1 hcpq false 0#usize)
      intro cr hcr
      have htc : cr = true ↔ Touches cw.val p1 := by
        rw [hcr]
        constructor
        · rintro (h | ⟨j, _, wk, c, hq, hs, hm⟩)
          · simp at h
          · exact ⟨wk, List.mem_of_getElem? hq, c, hs, hm⟩
        · rintro ⟨wk, hmem, c, hs, hm⟩
          obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
          exact Or.inr ⟨j, by simp, wk, c, by rw [List.getElem?_eq_getElem hj, hjw], hs, hm⟩
      have htw : Touches cw.val p1 ↔ Touches x.walkers.val p1 :=
        touches_drainW x.walkers.val x.patches.val p.val hcs cw.val hcwf hcwl p1
          (fun q _ pq' _ hd => hd.2)
      by_cases hcrt : cr = true
      · simp only [hcrt, ↓reduceIte]
        apply spec_bind (usize_succ_spec p (by have := x.patches.property; scalar_tac))
        intro p2 hp2
        rw [spec_ok]
        have hp2v : p2.val = p.val + 1 := hp2
        have hnd : ¬ Drains x.walkers.val p1 := fun hd => hd.2 (htw.mp (htc.mp hcrt))
        refine ⟨⟨cw, cp, rfl, ?_⟩, by show _ - p2.val < _ - p.val; omega⟩
        rw [hp2v]
        exact drainLists_skip x cw cp p.val p1 hlists hpm hpq hnd
      · simp only [hcrt, Bool.false_eq_true, ↓reduceIte]
        have hd : Drains x.walkers.val p1 :=
          ⟨hb.mp hbt, fun h => hcrt (htc.mpr (htw.mpr h))⟩
        simp only [alloc.vec.Vec.index_mut_slice_index]
        apply spec_bind (alloc.vec.Vec.index_mut_usize_spec cp p hl)
        rintro ⟨p2, back⟩ ⟨hp2, hback⟩
        have hp2e : p2 = p1 := by rw [hp2, hp1]
        subst hp2e
        subst hback
        have hset : (cp.set p { p2 with stage := shatter.Stage.Parked }).val[p.val]? =
            some { p2 with stage := shatter.Stage.Parked } := by
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_self hl]
        apply spec_bind (drain_park_spec (cp.set p { p2 with stage := shatter.Stage.Parked }) p
          { p2 with stage := shatter.Stage.Parked } hset cw cw 0#usize (by simp) rfl
          (fun i hi => by
            obtain ⟨o, ho, _⟩ := hcwf i (by omega)
            have hcwi : cw.val[i]? = some cw.val[i] := List.getElem?_eq_getElem (by omega)
            exact ⟨cw.val[i], hcwi, by simp [hcwi]⟩))
        intro cw' hcw'
        apply spec_bind (usize_succ_spec p (by have := x.patches.property; scalar_tac))
        intro p3 hp3
        rw [spec_ok]
        have hp3v : p3.val = p.val + 1 := hp3
        refine ⟨⟨cw', _, rfl, ?_⟩, by show _ - p3.val < _ - p.val; omega⟩
        rw [hp3v]
        exact drainLists_park x cw cp p p2 hlists hpm hpq hd cw' hcw'
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      apply spec_bind (usize_succ_spec p (by have := x.patches.property; scalar_tac))
      intro p2 hp2
      rw [spec_ok]
      have hp2v : p2.val = p.val + 1 := hp2
      have hnd : ¬ Drains x.walkers.val p1 := fun hd => hbt (hb.mpr hd.1)
      refine ⟨⟨cw, cp, rfl, ?_⟩, by show _ - p2.val < _ - p.val; omega⟩
      rw [hp2v]
      exact drainLists_skip x cw cp p.val p1 hlists hpm hpq hnd
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hpm : p.val = x.patches.val.length := by
      have : ¬ p.val < cp.val.length := hlt
      omega
    refine ⟨cw, cp, rfl, hcwl, hcpl, fun q hq => ?_, fun i hi => ?_⟩
    · obtain ⟨pq, hpq, hcq⟩ := hcp q hq
      refine ⟨pq, hpq, ?_⟩
      rw [hcq]; simp [hpm, hq]
    · obtain ⟨o, ho, hco⟩ := hcwf i hi
      exact ⟨o, ho, by rw [hco, hpm]⟩

/-- `drain_patches`: a draining patch with no crossing walker touching it is parked, and the walkers
standing in a parked patch are parked with it. Nothing else changes: not the other patches' stages,
cells or serials, not any crossing walker, not the holds, the tree, the routes or the stamp. -/
theorem drain_patches_spec (x : scene.Scene) (hcs : CrossAtSource x.walkers.val) :
    scene.Scene.drain_patches x ⦃ y =>
      ∃ cw cp, y = { x with walkers := cw, patches := cp } ∧
        cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
        (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
          cp.val[q]? = some (drainP x.walkers.val pq)) ∧
        (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
          cw.val[i]? = some (drainW x.walkers.val x.patches.val x.patches.val.length o)) ⦄ := by
  unfold scene.Scene.drain_patches
  apply spec_bind (Pₘ := fun y => ∃ cw cp, y = sceneFields { x with walkers := cw, patches := cp } ∧
        cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
        (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
          cp.val[q]? = some (drainP x.walkers.val pq)) ∧
        (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
          cw.val[i]? = some (drainW x.walkers.val x.patches.val x.patches.val.length o)))
  · unfold scene.Scene.drain_patches_loop0
    refine loop.spec_decr_nat (fun st : scene.Scene × Std.Usize =>
        x.patches.val.length - st.2.val)
      (fun st => DrainInv x st.1 st.2.val) _ _ _ ?_ ?_
    · rintro ⟨s, p⟩ hinv
      refine spec_mono (drain_patches_body_spec x hcs s p hinv) ?_
      intro r hr
      cases r <;> exact hr
    · refine ⟨x.walkers, x.patches, rfl, by simp, rfl, rfl, fun q hq => ?_, fun i hi => ?_⟩
      · obtain ⟨pq, hpq⟩ : ∃ pq, x.patches.val[q]? = some pq :=
          ⟨_, List.getElem?_eq_getElem hq⟩
        exact ⟨pq, hpq, by simp [hpq]⟩
      · obtain ⟨o, ho⟩ : ∃ o, x.walkers.val[i]? = some o := ⟨_, List.getElem?_eq_getElem hi⟩
        refine ⟨o, ho, ?_⟩
        simp [ho, drainW]
  · rintro ⟨l, t, w, v, v1, v2, v3, v4, v5, v6, s, i, i1, b, b1, b2, i2, o, i3⟩
      ⟨cw, cp, hy, h1, h2, h3, h4⟩
    simp only [sceneFields, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩ := hy
    exact (spec_ok _).mpr ⟨_, _, rfl, h1, h2, h3, h4⟩

end Labyrinth
