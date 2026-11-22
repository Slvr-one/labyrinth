module
public import LabyrinthCore.SceneShatterReform
public import LabyrinthCore.SceneShatterTick

/-! Shatter (S6), part 7: what the shatter operations change, and the order of a patch's stages.

The Rust keeps shatter state (patch stages, walker states, patch serials) apart from the passage
topology (`shatter.rs`: "separated from logical passage topology"). The theorems here confirm it:
`begin_shatter`, `hide_patch`, `scatter_patch` and `tick` never touch the tree, the routes, the
layout, the workspace, the published phases, the holds, or the freeze flags; they write patches,
walkers (stage-driven states only), the stamp, and, for `begin_shatter` and `reform_patch`, the trail
revision. `reform_patch` is the one operation that edits topology: it runs the same checked edit as a
motion or carve, and only on edges whose both ends lie in the patch. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The parts of a scene a shatter operation (other than `reform_patch`) never writes. -/
def ShatterFrame (self s : scene.Scene) : Prop :=
  s.layout = self.layout ∧ s.tree = self.tree ∧ s.work = self.work ∧ s.routes = self.routes ∧
  s.required = self.required ∧ s.phases = self.phases ∧ s.next_phases = self.next_phases ∧
  s.holds = self.holds ∧ s.clock = self.clock ∧ s.wall = self.wall ∧
  s.reanchor = self.reanchor ∧ s.suspended = self.suspended ∧ s.inactive = self.inactive ∧
  s.latest_request = self.latest_request ∧ s.pending = self.pending

theorem shatterFrame_refl (self : scene.Scene) : ShatterFrame self self :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every operation here either leaves the scene as it was (an error) or advances the revision by one
within the same epoch. -/
def Bumps (self s : scene.Scene) : Prop :=
  s.stamp.epoch = self.stamp.epoch ∧ s.stamp.revision.val = self.stamp.revision.val + 1

theorem stampRejects_err {α : Type _} {self : scene.Scene} {stamp : walker.Stamp}
    {res : core.result.Result α topology.Error × scene.Scene}
    (hn : ¬ StampAccepts self stamp) (hf : StampRejects self stamp res) :
    ∃ e, res = (.Err e, self) := by
  obtain ⟨f1, f2, f3⟩ := hf
  by_cases h1 : stamp.epoch = self.stamp.epoch
  · by_cases h2 : stamp.revision = self.stamp.revision
    · have h3 : self.stamp.revision.val = U64.max := by
        by_contra h3
        exact hn ⟨h1, h2, by have := self.stamp.revision.hBounds; scalar_tac⟩
      exact ⟨_, f3 h1 h2 h3⟩
    · exact ⟨_, f2 h1 h2⟩
  · exact ⟨_, f1 h1⟩

/-- What every result of a stamp-checked operation satisfies when it is an error. -/
def ErrKeeps {α : Type _} (self : scene.Scene)
    (res : core.result.Result α topology.Error × scene.Scene) : Prop :=
  ShatterFrame self res.2 ∧ ((∃ e, res.1 = .Err e) → res.2 = self)

theorem errKeeps_of {α : Type _} {self : scene.Scene} {e : topology.Error}
    {res : core.result.Result α topology.Error × scene.Scene} (h : res = (.Err e, self)) :
    ErrKeeps self res := by
  subst h; exact ⟨shatterFrame_refl _, fun _ => rfl⟩

theorem errKeeps_reject {α : Type _} {self : scene.Scene} {stamp : walker.Stamp}
    {res : core.result.Result α topology.Error × scene.Scene}
    (hn : ¬ StampAccepts self stamp) (hf : StampRejects self stamp res) : ErrKeeps self res := by
  obtain ⟨e, he⟩ := stampRejects_err hn hf
  exact errKeeps_of he

theorem begin_shatter_frame {self : scene.Scene} {stamp : walker.Stamp} {cells : Slice Std.Usize}
    {res : core.result.Result shatter.PatchId topology.Error × scene.Scene}
    (h : BsOutcome self stamp cells res) :
    ErrKeeps self res ∧
    (∀ id, res.1 = .Ok id → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
      res.2.trail_revision = res.2.stamp.revision ∧
      id.epoch = self.stamp.epoch ∧ id.serial = res.2.stamp.revision) := by
  have hok : ∀ e (s : scene.Scene), res = (.Err e, s) → s = self →
      ErrKeeps self res ∧ ∀ id, res.1 = .Ok id → False := by
    intro e s hr hs
    subst hs; subst hr
    exact ⟨errKeeps_of rfl, fun id hid => by simp at hid⟩
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · obtain ⟨e, he⟩ := stampRejects_err hn hf
    have := hok e self he rfl
    exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
  · rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · rcases h with ⟨e, _, h⟩ | ⟨_, h | ⟨slot, old, np, v, cw, cp, _, _, _, hv, _, _, h⟩⟩
      · have := hok _ _ h rfl
        exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
      · have := hok _ _ h.2 rfl
        exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
      · subst h
        have hfr : ShatterFrame self (shatteredScene self cw cp v) :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        refine ⟨⟨hfr, fun ⟨e, he⟩ => by simp at he⟩, fun id hid => ?_⟩
        simp only [core.result.Result.Ok.injEq] at hid
        subst hid
        exact ⟨hfr, ⟨rfl, by simp [shatteredScene, bumped, hv]⟩, rfl, rfl, rfl⟩

theorem hide_patch_frame {self : scene.Scene} {stamp : walker.Stamp} {id : shatter.PatchId}
    {res : core.result.Result walker.Stamp topology.Error × scene.Scene}
    (h : (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
      (StampAccepts self stamp ∧
        ((∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
         ∃ p, SlotOk self id p ∧
          ((Frozen self ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage ≠ shatter.Stage.Parked ∧
              res = (.Err topology.Error.Occupied, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Parked ∧
              ∃ (v : Std.U64) (ws : alloc.vec.Vec walker.Walker),
                v.val = self.stamp.revision.val + 1 ∧
                SweepOf p walker.WalkerState.Hidden self.walkers ws ∧
                res = (.Ok (bumped self v), hiddenScene self id p ws v)))))) :
    ErrKeeps self res ∧
    (∀ st, res.1 = .Ok st → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
      res.2.trail_revision = self.trail_revision ∧ st = res.2.stamp) := by
  have hok : ∀ e (s : scene.Scene), res = (.Err e, s) → s = self →
      ErrKeeps self res ∧ ∀ st, res.1 = .Ok st → False := by
    intro e s hr hs
    subst hs; subst hr
    exact ⟨errKeeps_of rfl, fun id hid => by simp at hid⟩
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · obtain ⟨e, he⟩ := stampRejects_err hn hf
    have := hok e self he rfl
    exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
  · rcases h with ⟨e, _, h⟩ | ⟨p, _, h | ⟨_, _, h⟩ | ⟨_, _, v, ws, hv, _, h⟩⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h.2 rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · subst h
      have hfr : ShatterFrame self (hiddenScene self id p ws v) :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨hfr, fun ⟨e, he⟩ => by simp at he⟩, fun st hst => ?_⟩
      simp only [core.result.Result.Ok.injEq] at hst
      subst hst
      exact ⟨hfr, ⟨rfl, by simp [hiddenScene, bumped, hv]⟩, rfl, rfl⟩

theorem scatter_patch_frame {self : scene.Scene} {stamp : walker.Stamp} {id : shatter.PatchId}
    {duration : Std.U64}
    {res : core.result.Result walker.Stamp topology.Error × scene.Scene}
    (h : (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
      (StampAccepts self stamp ∧
        ((∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
         ∃ p, SlotOk self id p ∧
          ((Frozen self ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage ≠ shatter.Stage.Hidden ∧
              res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val = 0 ∧
              res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val ≠ 0 ∧
              U64.max < self.clock.val + duration.val ∧
              res = (.Err topology.Error.Overflow, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val ≠ 0 ∧
              self.clock.val + duration.val ≤ U64.max ∧
              ∃ (v u : Std.U64), v.val = self.stamp.revision.val + 1 ∧
                u.val = self.clock.val + duration.val ∧
                res = (.Ok (bumped self v), scatteredScene self id p u v)))))) :
    ErrKeeps self res ∧
    (∀ st, res.1 = .Ok st → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
      res.2.trail_revision = self.trail_revision ∧ st = res.2.stamp) := by
  have hok : ∀ e (s : scene.Scene), res = (.Err e, s) → s = self →
      ErrKeeps self res ∧ ∀ st, res.1 = .Ok st → False := by
    intro e s hr hs
    subst hs; subst hr
    exact ⟨errKeeps_of rfl, fun id hid => by simp at hid⟩
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · obtain ⟨e, he⟩ := stampRejects_err hn hf
    have := hok e self he rfl
    exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
  · rcases h with ⟨e, _, h⟩ | ⟨p, _, h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, v, u, hv, _, h⟩⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h.2 rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · have := hok _ _ h rfl
      exact ⟨this.1, fun id hid => (this.2 id hid).elim⟩
    · subst h
      have hfr : ShatterFrame self (scatteredScene self id p u v) :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨hfr, fun ⟨e, he⟩ => by simp at he⟩, fun st hst => ?_⟩
      simp only [core.result.Result.Ok.injEq] at hst
      subst hst
      exact ⟨hfr, ⟨rfl, by simp [scatteredScene, bumped, hv]⟩, rfl, rfl⟩

/-! ### `reform_patch`: the one shatter operation that edits topology -/

/-- Every edge a successful reform edit removes or adds has both ends in the patch. -/
theorem not_outside_edges {p : shatter.Patch} {edit : scene.Edit} (h : ¬ OutsidePatch p edit) :
    ∀ e ∈ edit.remove.val ++ edit.add.val, PatchHas p e.u.val ∧ PatchHas p e.v.val := by
  intro e he
  by_contra hn
  apply h
  rcases List.mem_append.mp he with h1 | h1
  · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem h1
    exact Or.inl ⟨j, Nat.zero_le _, e, by rw [List.getElem?_eq_getElem hj, hjv], hn⟩
  · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem h1
    exact Or.inr ⟨j, Nat.zero_le _, e, by rw [List.getElem?_eq_getElem hj, hjv], hn⟩

/-- `reform_patch`, summarized: an error changes at most the scratch fields; a success edits the tree
by exactly the checked edit, with every edited edge inside the patch, and changes the patch's stage,
the stamp and the trail revision; the walkers, holds, clock and layout are untouched. -/
def ReformSummary (self : scene.Scene) (edit : scene.Edit) (id : shatter.PatchId)
    (duration : Std.U64) (res : core.result.Result walker.Stamp topology.Error × scene.Scene) :
    Prop :=
  EditSafe res.2 ∧
  ((∃ e, res.1 = .Err e) →
    ∃ req np wk, res.2 = { self with required := req, next_phases := np, work := wk }) ∧
  (∀ st, res.1 = .Ok st → ∃ (p : shatter.Patch) (u dl v : Std.U64),
    SlotOk self id p ∧ p.stage = shatter.Stage.Scattered u ∧ u.val ≤ self.clock.val ∧
    dl.val = self.clock.val + duration.val ∧ v.val = self.stamp.revision.val + 1 ∧
    (∀ e ∈ edit.remove.val ++ edit.add.val, PatchHas p e.u.val ∧ PatchHas p e.v.val) ∧
    res.2.layout = self.layout ∧ res.2.holds = self.holds ∧ res.2.walkers = self.walkers ∧
    res.2.clock = self.clock ∧ res.2.wall = self.wall ∧ res.2.phases = self.phases ∧
    res.2.reanchor = self.reanchor ∧ res.2.suspended = self.suspended ∧
    res.2.inactive = self.inactive ∧ res.2.pending = self.pending ∧
    (∀ a b, parentEdge (parents res.2.tree) a b ↔
      MutationEditedEdge (parents self.tree) edit.remove edit.add a b) ∧
    (edit.routes = none → res.2.routes = self.routes) ∧
    (∀ rs, edit.routes = some rs → allEdges res.2.routes.val = allEdges rs.val) ∧
    res.2.stamp = bumped self v ∧ res.2.trail_revision = v ∧
    res.2.patches = alloc.vec.Vec.set self.patches id.slot
      { p with stage := shatter.Stage.Reforming dl })

theorem reform_patch_headline (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit)
      (ReformSummary self edit id duration) := by
  refine okPost_mono (reform_patch_spec self stamp id duration edit hs hcap) ?_
  intro res h
  have hself : ∀ (e : topology.Error),
      res = (.Err e, self) → ReformSummary self edit id duration res := by
    intro e hr
    subst hr
    exact ⟨hs, fun _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
      fun st hst => by simp at hst⟩
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · obtain ⟨e, he⟩ := stampRejects_err hn hf
    exact hself e he
  · rcases h with ⟨e, _, h⟩ | ⟨p, hp, h⟩
    · exact hself e h
    · rcases h with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, ⟨u, hu, hule⟩, hdue⟩
      · exact hself _ h
      · exact hself _ h
      rcases hdue with ⟨_, h⟩ | ⟨hfit, dl, hdlv, hpl⟩
      · exact hself _ h
      · rcases hpl with ⟨_, h⟩ | ⟨hno, hg⟩
        · exact hself _ h
        · obtain ⟨hsafe, h | ⟨np, m, req, hnp, hpre, h | ⟨v, wk, t, ph, rt, hv, hk, h⟩⟩⟩ := hg
          · obtain ⟨np', x, pr, req', hnp', hpre', hpr, h⟩ := h
            subst h
            refine ⟨hsafe, fun _ => ⟨req', np', self.work, by rw [hpr]⟩, fun st hst => by simp at hst⟩
          · obtain ⟨x, wk', _, h⟩ := h
            subst h
            exact ⟨hsafe, fun _ => ⟨req, np, wk', rfl⟩, fun st hst => by simp at hst⟩
          · subst h
            refine ⟨hsafe, fun ⟨e, he⟩ => by simp at he, fun st hst => ?_⟩
            refine ⟨p, u, dl, v, hp, hu, hule, hdlv, hv, not_outside_edges hno, rfl, rfl, rfl, rfl, rfl,
              ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
            · exact hk.2.2.2.1
            · exact hk.2.1
            · exact hk.2.2.2.2.2.1
            · exact hk.2.2.2.2.2.2

/-! ### The order of a patch's stages -/

/-- The only stage changes there are: begin, drain, hide, scatter, reform, finish. -/
inductive StageNext : shatter.Stage → shatter.Stage → Prop
  | begin : StageNext shatter.Stage.Idle shatter.Stage.Draining
  | drain : StageNext shatter.Stage.Draining shatter.Stage.Parked
  | hide : StageNext shatter.Stage.Parked shatter.Stage.Hidden
  | scatter (u : Std.U64) : StageNext shatter.Stage.Hidden (shatter.Stage.Scattered u)
  | reform (u dl : Std.U64) :
      StageNext (shatter.Stage.Scattered u) (shatter.Stage.Reforming dl)
  | finish (u : Std.U64) : StageNext (shatter.Stage.Reforming u) shatter.Stage.Idle

/-- One `tick` moves each patch at most one step: a draining patch parks exactly when no crossing
walker touches it, a reforming patch whose deadline is reached becomes idle; cells and serial never
change. -/
theorem tick_patch_progress (z : Std.U64) (w : List walker.Walker) (p : shatter.Patch) :
    ((reformP z (drainP w p)).stage = p.stage ∨
      StageNext p.stage (reformP z (drainP w p)).stage) ∧
    (reformP z (drainP w p)).serial = p.serial ∧ (reformP z (drainP w p)).cells = p.cells ∧
    (p.stage = shatter.Stage.Draining → (reformP z (drainP w p)).stage = shatter.Stage.Parked →
      ¬ Touches w p) ∧
    (ExpiredP z p → (reformP z (drainP w p)).stage = shatter.Stage.Idle) := by
  classical
  by_cases hd : Drains w p
  · have hs : p.stage = shatter.Stage.Draining := hd.1
    have hdp : drainP w p = { p with stage := shatter.Stage.Parked } := by simp [drainP, hd]
    have hne : ¬ ExpiredP z { p with stage := shatter.Stage.Parked } := by
      rintro ⟨u, hu, _⟩; cases hu
    have hrp : reformP z { p with stage := shatter.Stage.Parked } =
        { p with stage := shatter.Stage.Parked } := by simp [reformP, hne]
    rw [hdp, hrp]
    refine ⟨Or.inr (by rw [hs]; exact StageNext.drain), rfl, rfl, fun _ _ => hd.2, ?_⟩
    rintro ⟨u, hu, _⟩; rw [hs] at hu; cases hu
  · have hdp : drainP w p = p := by simp [drainP, hd]
    rw [hdp]
    by_cases he : ExpiredP z p
    · obtain ⟨u, hu, _⟩ := he
      have hrp : reformP z p = { p with stage := shatter.Stage.Idle } := by
        simp [reformP, show ExpiredP z p from ⟨u, hu, by assumption⟩]
      rw [hrp]
      refine ⟨Or.inr (by rw [hu]; exact StageNext.finish u), rfl, rfl, ?_, fun _ => rfl⟩
      intro hs _
      exfalso; rw [hu] at hs; cases hs
    · have hrp : reformP z p = p := by simp [reformP, he]
      rw [hrp]
      exact ⟨Or.inl rfl, rfl, rfl, fun hs h2 => (by rw [hs] at h2; cases h2), fun h => absurd h he⟩

/-- Draining finishes, in that patch, exactly when nothing is crossing it, and the walkers standing in
a patch that finishes reforming are ready. -/
theorem reformW_ready (clock : Std.U64) (ps : List shatter.Patch) (k : Nat) (o : walker.Walker)
    (h : ∃ q, q < k ∧ ∃ pq, ps[q]? = some pq ∧ ExpiredP clock pq ∧ PatchHas pq o.cell.val) :
    (reformW clock ps k o).state = walker.WalkerState.Ready := by
  induction k with
  | zero => obtain ⟨q, hq, _⟩ := h; omega
  | succ k ih =>
    unfold reformW
    obtain ⟨q, hq, pq, hpq, hex, hhas⟩ := h
    cases hps : ps[k]? with
    | none =>
      simp only
      by_cases hqk : q = k
      · subst hqk; rw [hpq] at hps; cases hps
      · exact ih ⟨q, by omega, pq, hpq, hex, hhas⟩
    | some pk =>
      simp only
      split
      · by_cases hh : PatchHas pk (reformW clock ps k o).cell.val
        · simp [stateIf, hh]
        · simp only [stateIf, hh, ↓reduceIte]
          by_cases hqk : q = k
          · subst hqk
            rw [hpq] at hps; cases hps
            exact absurd (by rw [reformW_cell]; exact hhas) hh
          · exact ih ⟨q, by omega, pq, hpq, hex, hhas⟩
      · by_cases hqk : q = k
        · subst hqk; rw [hpq] at hps; cases hps; exact absurd hex ‹_›
        · exact ih ⟨q, by omega, pq, hpq, hex, hhas⟩

/-- The four stage steps the operations take, one each. -/
theorem op_stage_steps (p : shatter.Patch) (u dl : Std.U64) :
    (p.stage = shatter.Stage.Idle → StageNext p.stage shatter.Stage.Draining) ∧
    (p.stage = shatter.Stage.Parked → StageNext p.stage shatter.Stage.Hidden) ∧
    (p.stage = shatter.Stage.Hidden → StageNext p.stage (shatter.Stage.Scattered u)) ∧
    (p.stage = shatter.Stage.Scattered u → StageNext p.stage (shatter.Stage.Reforming dl)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h]
  · exact StageNext.begin
  · exact StageNext.hide
  · exact StageNext.scatter u
  · exact StageNext.reform u dl

/-- After `begin_shatter`, the new patch is draining (or already parked when nothing crosses it), and
every other patch is only drained: its stage can only go `Draining → Parked`. -/
theorem begin_shatter_patch {self : scene.Scene} {slot : Std.Usize} {np : shatter.Patch}
    {cw : alloc.vec.Vec walker.Walker} {cp : alloc.vec.Vec shatter.Patch}
    (hd : DrainOf (shatterStart self slot np) cw cp) (hl : slot.val < self.patches.val.length)
    (hnp : np.stage = shatter.Stage.Draining) :
    (∃ pq, cp.val[slot.val]? = some pq ∧ pq = drainP self.walkers.val np ∧
      (pq.stage = shatter.Stage.Draining ∨
        (pq.stage = shatter.Stage.Parked ∧ ¬ Touches self.walkers.val np))) ∧
    (∀ q, q < self.patches.val.length → q ≠ slot.val →
      cp.val[q]? = (self.patches.val[q]?).map (drainP self.walkers.val)) := by
  obtain ⟨_, hlp, hdp, _⟩ := hd
  have hlen : (shatterStart self slot np).patches.val.length = self.patches.val.length := by
    simp [shatterStart, alloc.vec.Vec.set_val_eq]
  have hw : (shatterStart self slot np).walkers = self.walkers := rfl
  rw [hw] at hdp
  refine ⟨?_, fun q hq hqs => ?_⟩
  · obtain ⟨pq, hpq, hc⟩ := hdp slot.val (by rw [hlen]; exact hl)
    have h1 : (shatterStart self slot np).patches.val[slot.val]? = some np := by
      simp only [shatterStart, alloc.vec.Vec.set_val_eq]
      rw [List.getElem?_set_self hl]
    rw [h1] at hpq; cases hpq
    refine ⟨_, hc, rfl, ?_⟩
    by_cases hdr : Drains self.walkers.val np
    · right; simp [drainP, hdr]; exact hdr.2
    · left; simp [drainP, hdr, hnp]
  · obtain ⟨pq, hpq, hc⟩ := hdp q (by rw [hlen]; exact hq)
    have h1 : (shatterStart self slot np).patches.val[q]? = self.patches.val[q]? := by
      simp only [shatterStart, alloc.vec.Vec.set_val_eq]
      rw [List.getElem?_set_ne (Ne.symm hqs)]
    rw [h1] at hpq
    rw [hc, hpq]; rfl

/-- A walker standing in a patch that finishes reforming is ready after the `tick`. -/
theorem tick_finishing_walkers_ready (z : Std.U64) (ps : List shatter.Patch) (o : walker.Walker)
    (q : Nat) (hq : q < ps.length) (pq : shatter.Patch) (hpq : ps[q]? = some pq)
    (hex : ExpiredP z pq) (hhas : PatchHas pq o.cell.val) :
    (reformW z ps ps.length o).state = walker.WalkerState.Ready :=
  reformW_ready z ps ps.length o ⟨q, hq, pq, hpq, hex, hhas⟩

/-! ### The headline: shatter never changes topology, except through `reform_patch`'s checked edit -/

theorem begin_shatter_headline (self : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
    (hcs : CrossAtSource self.walkers.val) (hroom : PatchRoom self) :
    scene.Scene.begin_shatter self stamp cells ⦃ res =>
      ErrKeeps self res ∧
      (∀ id, res.1 = .Ok id → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
        res.2.trail_revision = res.2.stamp.revision ∧
        id.epoch = self.stamp.epoch ∧ id.serial = res.2.stamp.revision) ⦄ :=
  spec_mono (begin_shatter_spec self stamp cells hcs hroom) (fun _ h => begin_shatter_frame h)

theorem hide_patch_headline (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId) :
    scene.Scene.hide_patch self stamp id ⦃ res =>
      ErrKeeps self res ∧
      (∀ st, res.1 = .Ok st → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
        res.2.trail_revision = self.trail_revision ∧ st = res.2.stamp) ⦄ :=
  spec_mono (hide_patch_spec self stamp id) (fun _ h => hide_patch_frame h)

theorem scatter_patch_headline (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) :
    scene.Scene.scatter_patch self stamp id duration ⦃ res =>
      ErrKeeps self res ∧
      (∀ st, res.1 = .Ok st → ShatterFrame self res.2 ∧ Bumps self res.2 ∧
        res.2.trail_revision = self.trail_revision ∧ st = res.2.stamp) ⦄ :=
  spec_mono (scatter_patch_spec self stamp id duration) (fun _ h => scatter_patch_frame h)

/-- `tick` on its active path never touches the tree, the routes, the layout, the workspace or the
published phases. -/
theorem tick_active_headline (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max) (hinv : ResInv self) :
    scene.Scene.tick self stamp wall ⦃ res =>
      (∃ st, res.1 = .Ok st) ∧
      res.2.layout = self.layout ∧ res.2.tree = self.tree ∧ res.2.work = self.work ∧
      res.2.routes = self.routes ∧ res.2.required = self.required ∧ res.2.phases = self.phases ∧
      res.2.next_phases = self.next_phases ∧ res.2.latest_request = self.latest_request ∧
      res.2.pending = self.pending ∧ res.2.trail_revision = self.trail_revision ∧
      Bumps self res.2 ⦄ := by
  refine spec_mono (tick_active_spec self stamp wall hacc hw hs hi hp hr hnov hinv) ?_
  rintro res ⟨v, z, hold, walk, cw, cp, hv, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [bumped, hv]⟩

end Labyrinth
