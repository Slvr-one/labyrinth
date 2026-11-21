module
public import LabyrinthCore.SceneHoldTick

/-! The hold law, part 3: the patch sweeps never touch a crossing walker.

`drain_patches` parks the walkers of a patch only once no crossing walker touches it, and the reform
step of `tick` readies the walkers of a patch that has finished draining, which `PatchClear` keeps
clear of crossings. So both sweeps rewrite only walkers that are not crossing (`SameCrossings`), and
both keep `PatchClear`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem drainP_cells (ws : List walker.Walker) (p : shatter.Patch) :
    (drainP ws p).cells = p.cells := by
  unfold drainP; split <;> rfl

theorem reformP_cells (z : Std.U64) (p : shatter.Patch) : (reformP z p).cells = p.cells := by
  unfold reformP; split <;> rfl

theorem touches_congr (ws : List walker.Walker) {p p' : shatter.Patch} (hc : p.cells = p'.cells)
    (h1 : p.stage ≠ shatter.Stage.Idle) (h2 : p'.stage ≠ shatter.Stage.Idle) :
    Touches ws p ↔ Touches ws p' := by
  have hh : ∀ cell, PatchHas p cell ↔ PatchHas p' cell := by
    intro cell; simp [PatchHas, hc, h1, h2]
  unfold Touches
  simp only [hh]

/-- A list given entry by entry as an image. -/
theorem list_eq_map {α β : Type _} (l : List α) (l' : List β) (f : α → β)
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → ∃ o, l[i]? = some o ∧ l'[i]? = some (f o)) :
    l' = l.map f := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < l.length
  · obtain ⟨o, ho, ho'⟩ := h i hi
    rw [ho', List.getElem?_map, ho]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem sameCrossings_map (ws : List walker.Walker) (f : walker.Walker → walker.Walker)
    (h : ∀ o ∈ ws, f o = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, (f o).state ≠ walker.WalkerState.Crossing c)) :
    SameCrossings ws (ws.map f) :=
  ⟨by simp, fun i hi => ⟨ws[i], f ws[i], List.getElem?_eq_getElem hi, by simp [hi],
    h _ (List.getElem_mem hi)⟩⟩

/-! ### `drain_patches` -/

theorem drainW_crossing (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (hcs : CrossAtSource ws) (o : walker.Walker) (ho : o ∈ ws) (c : walker.Crossing)
    (hc : o.state = walker.WalkerState.Crossing c) : drainW ws ps k o = o := by
  unfold drainW
  split
  · rename_i hex
    obtain ⟨q, _, pq, _, hd, hh⟩ := hex
    exact absurd ⟨o, ho, c, hc, Or.inl (by rw [← hcs o ho c hc]; exact hh)⟩ hd.2
  · rfl

theorem drainW_same (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (hcs : CrossAtSource ws) (o : walker.Walker) (ho : o ∈ ws) :
    drainW ws ps k o = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, (drainW ws ps k o).state ≠ walker.WalkerState.Crossing c) := by
  by_cases hx : ∃ c, o.state = walker.WalkerState.Crossing c
  · obtain ⟨c, hc⟩ := hx
    exact Or.inl (drainW_crossing ws ps k hcs o ho c hc)
  · rcases drainW_eq_or ws ps k o with e | e
    · exact Or.inl e
    · exact Or.inr ⟨fun c hc => hx ⟨c, hc⟩, e⟩

/-- Draining keeps every settled patch clear: a patch it parks had no crossing walker touching it. -/
theorem drain_clear {ws cw : List walker.Walker} {ps : List shatter.Patch}
    (h : PatchClearL ws ps) (hs : CrossSub ws cw) : PatchClearL cw (ps.map (drainP ws)) := by
  intro p hp h1 h2 ht
  obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hp
  have ht' := touches_crossSub hs _ ht
  by_cases hd : Drains ws pq
  · have e : drainP ws pq = { pq with stage := shatter.Stage.Parked } := by
      unfold drainP; simp only [hd, ↓reduceIte]
    rw [e] at h1 ht'
    have hpd : pq.stage = shatter.Stage.Draining := hd.1
    exact hd.2 ((touches_congr ws (p := { pq with stage := shatter.Stage.Parked }) (p' := pq) rfl h1
      (by rw [hpd]; simp)).mp ht')
  · have e : drainP ws pq = pq := by unfold drainP; simp only [hd, ↓reduceIte]
    rw [e] at h1 h2 ht'
    exact h pq hpq h1 h2 ht'

/-! ### The reform step of `tick` -/

theorem reformW_keep (z : Std.U64) (ps : List shatter.Patch) (o : walker.Walker)
    (hno : ∀ (q : Nat) (p : shatter.Patch), ps[q]? = some p → ExpiredP z p → ¬ PatchHas p o.cell.val) (k : Nat) :
    reformW z ps k o = o := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold reformW
    cases hps : ps[k]? with
    | none => exact ih
    | some p =>
      simp only
      split
      · rename_i hexp
        rw [ih]
        simp [stateIf, hno k p hps hexp]
      · exact ih

theorem expired_settled {z : Std.U64} {p : shatter.Patch} (h : ExpiredP z p) :
    p.stage ≠ shatter.Stage.Idle ∧ p.stage ≠ shatter.Stage.Draining := by
  obtain ⟨u, hu, _⟩ := h
  rw [hu]; exact ⟨by simp, by simp⟩

theorem reformW_same (z : Std.U64) (ws : List walker.Walker) (ps : List shatter.Patch) (k : Nat)
    (hcs : CrossAtSource ws) (hcl : PatchClearL ws ps) (o : walker.Walker) (ho : o ∈ ws) :
    reformW z ps k o = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, (reformW z ps k o).state ≠ walker.WalkerState.Crossing c) := by
  by_cases hx : ∃ c, o.state = walker.WalkerState.Crossing c
  · obtain ⟨c, hc⟩ := hx
    refine Or.inl (reformW_keep z ps o (fun q p hq hexp hh => ?_) k)
    obtain ⟨h1, h2⟩ := expired_settled hexp
    exact hcl p (List.mem_of_getElem? hq) h1 h2
      ⟨o, ho, c, hc, Or.inl (by rw [← hcs o ho c hc]; exact hh)⟩
  · rcases reformW_eq_or z ps k o with e | e
    · exact Or.inl e
    · exact Or.inr ⟨fun c hc => hx ⟨c, hc⟩, e⟩

/-- The reform step keeps every settled patch clear: it only makes patches idle. -/
theorem reform_clear (z : Std.U64) {ws cw : List walker.Walker} {ps : List shatter.Patch}
    (h : PatchClearL ws ps) (hs : CrossSub ws cw) : PatchClearL cw (ps.map (reformP z)) := by
  intro p hp h1 h2 ht
  obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hp
  have ht' := touches_crossSub hs _ ht
  by_cases hx : ExpiredP z pq
  · have e : reformP z pq = { pq with stage := shatter.Stage.Idle } := by
      unfold reformP; simp only [hx, ↓reduceIte]
    rw [e] at h1
    exact h1 rfl
  · have e : reformP z pq = pq := by unfold reformP; simp only [hx, ↓reduceIte]
    rw [e] at h1 h2 ht'
    exact h pq hpq h1 h2 ht'

/-- A composite of two sweeps that each rewrite only non-crossing walkers. -/
theorem same_comp {o m n : walker.Walker}
    (h1 : m = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, m.state ≠ walker.WalkerState.Crossing c))
    (h2 : m = o → n = o)
    (h3 : (∀ c, m.state ≠ walker.WalkerState.Crossing c) →
      ∀ c, n.state ≠ walker.WalkerState.Crossing c) :
    n = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, n.state ≠ walker.WalkerState.Crossing c) := by
  rcases h1 with e | ⟨ho, hm⟩
  · exact Or.inl (h2 e)
  · exact Or.inr ⟨ho, h3 hm⟩

end Labyrinth
