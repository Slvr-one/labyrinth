module
public import LabyrinthCore.SceneStd

public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
open Aeneas.Data.Coinductive

namespace Labyrinth

section PartialLoop

unseal Result

/-- Weakest precondition that treats failure as vacuously fine. -/
@[expose, reducible] def laxWP : EffectWP RustEffect where
  State := Unit
  wp _ _ _ := True

instance laxMono : EffectWP.Monotonic laxWP where
  wp_monotonic := by intros; trivial

instance laxConj : EffectWP.Conjunctive laxWP where
  wp_conj := by intros; trivial

@[expose] def lax {α} (m : Result α) (p : α → Prop) : Prop :=
  DWLP laxWP m (fun v _ => p v) ()

theorem lax_admissible {α} (p : α → Prop) : Lean.Order.admissible (fun m : Result α => lax m p) :=
  DWLP.admissible laxWP _ ()

theorem lax_of_ok_imp {α} (m : Result α) (p : α → Prop) (h : ∀ r, m = ok r → p r) : lax m p := by
  cases m using Result.cases with
  | ret r => exact (DWLP.ret_iff (θ := laxWP) (value := r)).mpr (h r rfl)
  | vis i k => exact DWLP.vis (θ := laxWP) trivial
  | div => exact DWLP.div (θ := laxWP)


theorem lax_of_ok {α} (m : Result α) (p : α → Prop) (y : α) (h : m = ok y) (hl : lax m p) : p y := by
  subst h
  exact (DWLP.ret_iff (θ := laxWP) (value := y)).mp hl

theorem loop_lax {α β : Type _} (body : α → Result (ControlFlow α β)) (inv : α → Prop)
    (post : β → Prop)
    (hb : ∀ x, inv x → ∀ r, body x = ok r →
      match r with | .done y => post y | .cont x' => inv x')
    (x : α) (hx : inv x) : lax (loop body x) post := by
  have key : ∀ x, inv x → lax (loop body x) post := by
    have := loop.fixpoint_induct body (fun f => ∀ x, inv x → lax (f x) post) ?adm ?step
    · exact this
    · exact Lean.Order.admissible_pi_apply (fun x (m : Result β) => inv x → lax m post)
        (fun x => Lean.Order.admissible_pi (fun (m : Result β) (_ : inv x) => lax m post)
          (fun _ => lax_admissible post))
    · intro f ih x hx
      have hbx := hb x hx
      show lax (Std.bind (body x) (fun r => match r with
        | ControlFlow.cont x => f x | ControlFlow.done x => ok x)) post
      cases hbd : body x using Result.cases with
      | ret r =>
        rw [hbd] at hbx
        have hr := hbx r rfl
        rw [Std.bind_ok]
        cases r with
        | done y' => exact (DWLP.ret_iff (θ := laxWP) (value := y')).mpr hr
        | cont x' => exact ih x' hr
      | vis i k =>
        change DWLP laxWP (ITree.bind (ITree.vis i k) _) _ ()
        erw [itree_vis_bind]
        exact DWLP.vis (θ := laxWP) trivial
      | div =>
        change DWLP laxWP (ITree.bind ITree.div _) _ ()
        erw [itree_div_bind]
        exact DWLP.div (θ := laxWP)
  exact key x hx


theorem lax_bind {α β : Type _} {m : Result α} {k : α → Result β} {P : α → Prop} {Q : β → Prop}
    (hm : lax m P) (hk : ∀ a, P a → lax (k a) Q) : lax (Std.bind m k) Q :=
  DWLP.bind (θ := laxWP) hm (fun v _ h => hk v h)

theorem lax_triv {α : Type _} (m : Result α) : lax m (fun _ => True) :=
  lax_of_ok_imp _ _ (fun _ _ => trivial)

theorem lax_ok {α : Type _} {Q : α → Prop} (x : α) (h : Q x) : lax (ok x) Q :=
  (DWLP.ret_iff (θ := laxWP) (value := x)).mpr h

end PartialLoop

/-! ### `check_stamp` -/

theorem check_stamp_stale_epoch (self : scene.Scene) (stamp : walker.Stamp)
    (h : stamp.epoch ≠ self.stamp.epoch) :
    scene.Scene.check_stamp self stamp = ok (.Err topology.Error.StaleEpoch) := by
  unfold scene.Scene.check_stamp
  simp [h, bne_iff_ne]

theorem check_stamp_stale_revision (self : scene.Scene) (stamp : walker.Stamp)
    (h1 : stamp.epoch = self.stamp.epoch) (h2 : stamp.revision ≠ self.stamp.revision) :
    scene.Scene.check_stamp self stamp = ok (.Err topology.Error.StaleRevision) := by
  unfold scene.Scene.check_stamp
  simp [h1, h2, bne_iff_ne]

theorem check_stamp_overflow (self : scene.Scene) (stamp : walker.Stamp)
    (h1 : stamp.epoch = self.stamp.epoch) (h2 : stamp.revision = self.stamp.revision)
    (h3 : self.stamp.revision.val = U64.max) :
    scene.Scene.check_stamp self stamp = ok (.Err topology.Error.Overflow) := by
  unfold scene.Scene.check_stamp
  have hc := U64.checked_add_bv_spec self.stamp.revision 1#u64
  simp only [h1, h2, bne_self_eq_false, Bool.false_eq_true, ite_false, lift, bind_ok]
  cases hco : U64.checked_add self.stamp.revision 1#u64 with
  | none => simp [core.option.Option.ok_or]
  | some z =>
    rw [hco] at hc
    simp at hc
    omega

theorem check_stamp_ok (self : scene.Scene) (stamp : walker.Stamp)
    (h1 : stamp.epoch = self.stamp.epoch) (h2 : stamp.revision = self.stamp.revision)
    (h3 : self.stamp.revision.val < U64.max) :
    ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
      scene.Scene.check_stamp self stamp = ok (.Ok v) := by
  unfold scene.Scene.check_stamp
  have hc := U64.checked_add_bv_spec self.stamp.revision 1#u64
  simp only [h1, h2, bne_self_eq_false, Bool.false_eq_true, ite_false, lift, bind_ok]
  cases hco : U64.checked_add self.stamp.revision 1#u64 with
  | none =>
    rw [hco] at hc
    simp at hc
    omega
  | some z =>
    rw [hco] at hc
    simp at hc
    exact ⟨z, by omega, by simp [core.option.Option.ok_or]⟩

/-- The checked stamp comparison: epoch first, then revision, then the successor of the revision. -/
theorem check_stamp_spec (self : scene.Scene) (stamp : walker.Stamp) :
    scene.Scene.check_stamp self stamp ⦃ r =>
      (stamp.epoch ≠ self.stamp.epoch → r = .Err topology.Error.StaleEpoch) ∧
      (stamp.epoch = self.stamp.epoch → stamp.revision ≠ self.stamp.revision →
        r = .Err topology.Error.StaleRevision) ∧
      (stamp.epoch = self.stamp.epoch → stamp.revision = self.stamp.revision →
        self.stamp.revision.val = U64.max → r = .Err topology.Error.Overflow) ∧
      (stamp.epoch = self.stamp.epoch → stamp.revision = self.stamp.revision →
        self.stamp.revision.val < U64.max →
        ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧ r = .Ok v) ⦄ := by
  by_cases h1 : stamp.epoch = self.stamp.epoch
  · by_cases h2 : stamp.revision = self.stamp.revision
    · by_cases h3 : self.stamp.revision.val = U64.max
      · rw [check_stamp_overflow self stamp h1 h2 h3, spec_ok]
        exact ⟨fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ _ => rfl,
          fun _ _ h => absurd h3 (by omega)⟩
      · have h3' : self.stamp.revision.val < U64.max := by
          have hle : self.stamp.revision.val ≤ U64.max := by scalar_tac
          omega
        obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3'
        rw [he, spec_ok]
        exact ⟨fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ h => absurd h h3,
          fun _ _ _ => ⟨v, hv, rfl⟩⟩
    · rw [check_stamp_stale_revision self stamp h1 h2, spec_ok]
      exact ⟨fun h => absurd h1 h, fun _ _ => rfl, fun _ h => absurd h h2,
        fun _ h => absurd h h2⟩
  · rw [check_stamp_stale_epoch self stamp h1, spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd h h1, fun h => absurd h h1, fun h => absurd h h1⟩


/-! ### Shared shape of the stamp-checked operations -/

/-- The stamp is the scene's current one and its revision has a successor. -/
def StampAccepts (self : scene.Scene) (stamp : walker.Stamp) : Prop :=
  stamp.epoch = self.stamp.epoch ∧ stamp.revision = self.stamp.revision ∧
    self.stamp.revision.val < U64.max

/-- The three failures of `check_stamp`, in order, each leaving the scene unchanged. -/
def StampRejects {α : Type _} (self : scene.Scene) (stamp : walker.Stamp)
    (res : core.result.Result α topology.Error × scene.Scene) : Prop :=
  (stamp.epoch ≠ self.stamp.epoch → res = (.Err topology.Error.StaleEpoch, self)) ∧
  (stamp.epoch = self.stamp.epoch → stamp.revision ≠ self.stamp.revision →
    res = (.Err topology.Error.StaleRevision, self)) ∧
  (stamp.epoch = self.stamp.epoch → stamp.revision = self.stamp.revision →
    self.stamp.revision.val = U64.max → res = (.Err topology.Error.Overflow, self))

/-- The stamp returned on success: the current epoch and the successor revision. -/
def bumped (self : scene.Scene) (v : Std.U64) : walker.Stamp := { self.stamp with revision := v }

theorem stamp_rejects_of_accepts {α : Type _} {self : scene.Scene} {stamp : walker.Stamp}
    (h : StampAccepts self stamp) (res : core.result.Result α topology.Error × scene.Scene) :
    StampRejects self stamp res := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ h => absurd h (by omega)⟩

/-- Reduction of a stamp-checked operation: the check's three failures return unchanged, success
continues with the successor revision. -/
theorem stamp_gate {α : Type _} (self : scene.Scene) (stamp : walker.Stamp)
    (K : Std.U64 → Result (core.result.Result α topology.Error × scene.Scene))
    (P : core.result.Result α topology.Error × scene.Scene → Prop)
    (hok : ∀ v : Std.U64, v.val = self.stamp.revision.val + 1 → StampAccepts self stamp → spec (K v) P)
    (hrej : ∀ res, ¬ StampAccepts self stamp → StampRejects self stamp res → P res) :
    spec (do
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
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        apply hrej _ (fun h => by obtain ⟨_, _, h3'⟩ := h; omega)
        exact ⟨fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ _ => rfl⟩
      · obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 (by omega)
        rw [he]
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        exact hok v hv ⟨h1, h2, by omega⟩
    · rw [check_stamp_stale_revision self stamp h1 h2]
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      apply hrej _ (fun h => h2 h.2.1)
      exact ⟨fun h => absurd h1 h, fun _ _ => rfl, fun _ h => absurd h h2⟩
  · rw [check_stamp_stale_epoch self stamp h1]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    apply hrej _ (fun h => h1 h.1)
    exact ⟨fun _ => rfl, fun h => absurd h h1, fun h => absurd h h1⟩

/-! ### `suspend` and `resume` -/

theorem suspend_spec (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) :
    scene.Scene.suspend self stamp wall ⦃ res =>
      StampRejects self stamp res ∧
      (StampAccepts self stamp → wall.val < self.wall.val →
        res = (.Err topology.Error.InvalidTransition, self)) ∧
      (StampAccepts self stamp → self.wall.val ≤ wall.val →
        ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
          res = (.Ok (bumped self v),
            { self with stamp := bumped self v, wall := wall, suspended := true })) ⦄ := by
  unfold scene.Scene.suspend
  apply stamp_gate
  · intro v hv hacc
    by_cases hw : wall < self.wall
    · simp only [hw, ite_true, spec_ok]
      refine ⟨stamp_rejects_of_accepts hacc _, fun _ _ => trivial, fun _ h => ?_⟩
      simp at hw
      omega
    · simp only [hw, ite_false, spec_ok]
      simp at hw
      refine ⟨stamp_rejects_of_accepts hacc _, fun _ h => ?_, fun _ _ => ⟨v, hv, rfl⟩⟩
      omega
  · intro res hn hr
    exact ⟨hr, fun h => absurd h hn, fun h => absurd h hn⟩

theorem resume_spec (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) :
    scene.Scene.resume self stamp wall ⦃ res =>
      StampRejects self stamp res ∧
      (StampAccepts self stamp → wall.val < self.wall.val →
        res = (.Err topology.Error.InvalidTransition, self)) ∧
      (StampAccepts self stamp → self.wall.val ≤ wall.val →
        ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
          res = (.Ok (bumped self v),
            { self with stamp := bumped self v, wall := wall,
                        reanchor := (self.pending.isSome || self.inactive),
                        suspended := false })) ⦄ := by
  unfold scene.Scene.resume
  apply stamp_gate
  · intro v hv hacc
    by_cases hw : wall < self.wall
    · simp only [hw, ite_true, spec_ok]
      refine ⟨stamp_rejects_of_accepts hacc _, fun _ _ => trivial, fun _ h => ?_⟩
      simp at hw
      omega
    · have hw2 : self.wall.val ≤ wall.val := by simpa using hw
      simp only [hw, ite_false]
      cases hp : self.pending <;>
        simp [core.option.Option.is_some, spec_ok, stamp_rejects_of_accepts hacc, bumped, hw2, hv]
  · intro res hn hr
    exact ⟨hr, fun h => absurd h hn, fun h => absurd h hn⟩

/-! ### `request_layout` -/

theorem u64_checked_succ (x : Std.U64) :
    (x.val = U64.max ∧ U64.checked_add x 1#u64 = none) ∨
    (∃ z : Std.U64, x.val < U64.max ∧ z.val = x.val + 1 ∧ U64.checked_add x 1#u64 = some z) := by
  have hc := U64.checked_add_bv_spec x 1#u64
  have hle : x.val ≤ U64.max := by scalar_tac
  cases hco : U64.checked_add x 1#u64 with
  | none =>
    rw [hco] at hc
    simp at hc
    exact Or.inl ⟨by omega, rfl⟩
  | some z =>
    rw [hco] at hc
    simp at hc
    exact Or.inr ⟨z, by omega, by omega, rfl⟩

theorem request_layout_spec (self : scene.Scene) (stamp : walker.Stamp) :
    scene.Scene.request_layout self stamp ⦃ res =>
      StampRejects self stamp res ∧
      (StampAccepts self stamp → self.latest_request.val = U64.max →
        res = (.Err topology.Error.Overflow, self)) ∧
      (StampAccepts self stamp → self.latest_request.val < U64.max →
        ∃ v req : Std.U64, v.val = self.stamp.revision.val + 1 ∧
          req.val = self.latest_request.val + 1 ∧
          res = (.Ok req,
            { self with stamp := bumped self v, reanchor := true, latest_request := req,
                        pending := some req })) ⦄ := by
  unfold scene.Scene.request_layout
  apply stamp_gate
  · intro v hv hacc
    simp only [lift, bind_ok]
    rcases u64_checked_succ self.latest_request with ⟨hm, hn⟩ | ⟨z, hlt, hz, hs⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok,
        stamp_rejects_of_accepts hacc, hm]
    · rw [hs]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, spec_ok,
        stamp_rejects_of_accepts hacc]
      refine ⟨fun _ => by omega, fun _ _ => ⟨v, hv, hz, rfl⟩⟩
  · intro res hn hr
    exact ⟨hr, fun h => absurd h hn, fun h => absurd h hn⟩

/-! ### `publish_layout` -/

/-- A walker in the middle of a crossing, which holds reservations. -/
def isCrossing (w : walker.Walker) : Bool :=
  match w.state with
  | walker.WalkerState.Crossing _ => true
  | _ => false

/-- The number of crossing walkers in a list. -/
def crossCount (l : List walker.Walker) : Nat := l.countP isCrossing

theorem publish_layout_loop_spec (orig : alloc.vec.Vec walker.Walker) :
    ∀ (v : alloc.vec.Vec walker.Walker) (i w : Std.Usize),
      v.length = orig.length → w.val ≤ orig.length →
      v.val.drop w.val = orig.val.drop w.val →
      i.val + crossCount (orig.val.drop w.val) = crossCount orig.val →
      scene.Scene.publish_layout_loop v i w ⦃ n => n.val = crossCount orig.val ⦄ := by
  intro v i w hlen hw hdrop hcount
  unfold scene.Scene.publish_layout_loop
  refine loop.spec_decr_nat (fun x : (alloc.vec.Vec walker.Walker × Std.Usize × Std.Usize) =>
      orig.length - x.2.2.val)
    (fun x => x.1.length = orig.length ∧ x.2.2.val ≤ orig.length ∧
      x.1.val.drop x.2.2.val = orig.val.drop x.2.2.val ∧
      x.2.1.val + crossCount (orig.val.drop x.2.2.val) = crossCount orig.val)
    (fun n : Std.Usize => n.val = crossCount orig.val) _ _ ?_ ⟨hlen, hw, hdrop, hcount⟩
  rintro ⟨v, i, w⟩ ⟨hlen, hw, hdrop, hcount⟩
  simp only at hlen hw hdrop hcount
  unfold scene.Scene.publish_layout_loop.body
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  by_cases hlt : w < alloc.vec.Vec.len v
  · simp only [hlt, ite_true]
    have hwl : w.val < orig.length := by simpa [hlen] using hlt
    have hwv : w.val < v.length := by omega
    apply spec_bind (alloc.vec.Vec.index_usize_spec v w hwv)
    intro w1 hw1
    have hdrop1 : v.val.drop w.val = v.val[w.val] :: v.val.drop (w.val + 1) :=
      List.drop_eq_getElem_cons hwv
    have hdrop2 : orig.val.drop w.val = orig.val[w.val] :: orig.val.drop (w.val + 1) :=
      List.drop_eq_getElem_cons hwl
    have hw1o : w1 = orig.val[w.val] := by
      rw [hdrop1, hdrop2] at hdrop
      rw [hw1]
      exact (List.cons.inj hdrop).1
    have hcc : crossCount (orig.val.drop w.val) =
        (if isCrossing w1 then 1 else 0) + crossCount (orig.val.drop (w.val + 1)) := by
      rw [hdrop2, ← hw1o]
      simp [crossCount, List.countP_cons]
      omega
    have hccle : crossCount orig.val ≤ orig.length := List.countP_le_length
    have hmax : orig.length ≤ Usize.max := orig.property
    have hi2 : (match w1.state with
        | walker.WalkerState.Ready => ok i
        | walker.WalkerState.Crossing _ => i + 1#usize
        | walker.WalkerState.Parked => ok i
        | walker.WalkerState.Hidden => ok i
        | walker.WalkerState.Terminated => ok i) ⦃ i2 =>
          i2.val + crossCount (orig.val.drop (w.val + 1)) = crossCount orig.val ⦄ := by
      cases hs : w1.state with
      | Crossing c =>
        have hc : isCrossing w1 = true := by simp [isCrossing, hs]
        rw [hc] at hcc
        simp only [ite_true] at hcc
        simp only
        apply spec_mono (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
        intro z hz
        simp at hz
        omega
      | Ready =>
        have hc : isCrossing w1 = false := by simp [isCrossing, hs]
        rw [hc] at hcc
        simp only [Bool.false_eq_true, ite_false] at hcc
        simp [spec_ok]; omega
      | Parked =>
        have hc : isCrossing w1 = false := by simp [isCrossing, hs]
        rw [hc] at hcc
        simp only [Bool.false_eq_true, ite_false] at hcc
        simp [spec_ok]; omega
      | Hidden =>
        have hc : isCrossing w1 = false := by simp [isCrossing, hs]
        rw [hc] at hcc
        simp only [Bool.false_eq_true, ite_false] at hcc
        simp [spec_ok]; omega
      | Terminated =>
        have hc : isCrossing w1 = false := by simp [isCrossing, hs]
        rw [hc] at hcc
        simp only [Bool.false_eq_true, ite_false] at hcc
        simp [spec_ok]; omega
    apply spec_bind hi2
    intro i2 hi2v
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec v w hwv)
    rintro ⟨w2, back⟩ ⟨hw2, rfl⟩
    apply spec_bind (Usize.add_spec (x := w) (y := 1#usize) (by simp; omega))
    intro w3 hw3
    simp at hw3
    rw [spec_ok]
    simp only
    refine ⟨⟨by simp [hlen], by omega, ?_, ?_⟩, by omega⟩
    · simp [hw3, alloc.vec.Vec.set_val_eq]
      have h1 : v.val.drop (w.val + 1) = orig.val.drop (w.val + 1) := by
        have := hdrop
        rw [hdrop1, hdrop2] at this
        exact (List.cons.inj this).2
      rw [← h1]
      exact List.drop_set_of_lt (by omega)
    · simpa [hw3] using hi2v
  · simp only [hlt, ite_false, spec_ok]
    have hlt' : ¬ (w.val < v.length) := fun h => hlt (by simpa using h)
    have : w.val = orig.length := by omega
    rw [this] at hcount
    simp [crossCount] at hcount
    simpa [crossCount] using hcount

theorem publish_layout_spec (self : scene.Scene) (request : Std.U64) (candidate : scene.Scene) :
    scene.Scene.publish_layout self request candidate ⦃ res =>
      (self.pending ≠ some request →
        res = (.Err topology.Error.StaleEpoch, self)) ∧
      (self.pending = some request → self.latest_request ≠ request →
        res = (.Err topology.Error.StaleEpoch, self)) ∧
      (self.pending = some request → self.latest_request = request →
        candidate.stamp.epoch ≠ request →
        res = (.Err topology.Error.StaleEpoch, self)) ∧
      (self.pending = some request → self.latest_request = request →
        candidate.stamp.epoch = request → candidate.stamp.revision ≠ 0#u64 →
        res = (.Err topology.Error.InvalidTransition, self)) ∧
      (self.pending = some request → self.latest_request = request →
        candidate.stamp.epoch = request → candidate.stamp.revision = 0#u64 →
        ∃ terminated released : Std.Usize,
          terminated.val = self.walkers.length ∧
          released.val = crossCount self.walkers.val ∧
          res = (.Ok { epoch := self.stamp.epoch, terminated_walkers := terminated,
                       released_reservations := released },
            { candidate with wall := self.wall, reanchor := true,
                             suspended := self.suspended, latest_request := request })) ⦄ := by
  unfold scene.Scene.publish_layout
  apply spec_bind (core.cmp.PartialEq.ne.trait_default.spec
    (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
    self.pending (some request) (option_eq_u64_spec _ _))
  intro b hb
  by_cases h1 : self.pending = some request
  · have hbf : b = false := by
      cases b
      · rfl
      · exact absurd h1 (hb.mp rfl)
    subst hbf
    simp only [Bool.false_eq_true, ite_false]
    by_cases h2 : self.latest_request = request
    · by_cases h3 : candidate.stamp.epoch = request
      · by_cases h4 : candidate.stamp.revision = 0#u64
        · simp only [h2, h3, h4, bne_self_eq_false, Bool.false_eq_true, ite_false]
          apply spec_bind (publish_layout_loop_spec self.walkers self.walkers 0#usize 0#usize
            rfl (by simp) rfl (by simp))
          intro n hn
          simp only [lift, bind_ok]
          generalize hdm : self.holds.deref_mut = dm
          obtain ⟨sl, back⟩ := dm
          apply spec_bind (core.slice.Slice.fill.spec core.clone.CloneUsize sl 0#usize
            (by simp [spec_ok]))
          intro s' hs'
          rw [spec_ok]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intros; simp_all
          · intros; simp_all
          · intros; simp_all
          · intros; simp_all
          · intros
            exact ⟨self.walkers.len, n, by simp, hn, rfl⟩
        · simp only [h2, h3, bne_self_eq_false, Bool.false_eq_true, ite_false, bne_iff_ne, ne_eq,
            h4, not_false_eq_true, ite_true, spec_ok]
          simp_all
      · simp only [h2, bne_self_eq_false, Bool.false_eq_true, ite_false, bne_iff_ne, ne_eq, h3,
          not_false_eq_true, ite_true, spec_ok]
        simp_all
    · simp only [bne_iff_ne, ne_eq, h2, not_false_eq_true, ite_true, spec_ok]
      simp_all
  · have hbt : b = true := hb.mpr h1
    subst hbt
    simp only [ite_true, spec_ok]
    simp_all

/-! ### `reject_layout` -/

theorem spec_eq_ok {α : Type _} {m : Result α} {P : α → Prop} (h : spec m P) :
    ∃ v, m = ok v ∧ P v := by
  cases m using Result.cases with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by rw [spec_vis]; exact id)
  | div => exact absurd h (by simp)

theorem pending_ne_eval (pending : Option Std.U64) (request : Std.U64) :
    core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
      pending (some request) = ok (decide (pending ≠ some request)) := by
  obtain ⟨b, hb, hP⟩ := spec_eq_ok (core.cmp.PartialEq.ne.trait_default.spec
    (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
    pending (some request) (option_eq_u64_spec _ _))
  rw [hb]
  congr 1
  cases b <;> simp_all

theorem reject_layout_stale_pending (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
    (h : self.pending ≠ some request) :
    scene.Scene.reject_layout self request viewport =
      ok (.Err topology.Error.StaleEpoch, self) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  simp [h]

theorem reject_layout_stale_latest (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
    (hp : self.pending = some request) (h : self.latest_request ≠ request) :
    scene.Scene.reject_layout self request viewport =
      ok (.Err topology.Error.StaleEpoch, self) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  simp [hp, h, bne_iff_ne]

/-- The scan of the retired tree against the new viewport, as `reject_layout` performs it. -/
def rejectScan (self : scene.Scene) (viewport : grid.Rect) :
    Result (Bool × core.result.Result Unit topology.Error) :=
  scene.Scene.reject_layout_loop self.layout self.tree self.work self.routes self.required
    self.phases self.next_phases self.holds self.walkers self.patches self.stamp.epoch
    self.stamp.revision self.clock self.wall self.reanchor self.suspended self.inactive
    self.latest_request self.pending self.trail_revision viewport true (core.result.Result.Ok ())
    0#usize

theorem reject_layout_invalid_viewport (self : scene.Scene) (request : Std.U64)
    (viewport : grid.Rect) (hp : self.pending = some request) (hl : self.latest_request = request)
    (e : topology.Error) (hv : grid.Rect.validate viewport = ok (.Err e)) :
    scene.Scene.reject_layout self request viewport = ok (.Err e, self) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  simp [hp, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem reject_layout_overflow (self : scene.Scene) (request : Std.U64)
    (viewport : grid.Rect) (hp : self.pending = some request) (hl : self.latest_request = request)
    (hv : grid.Rect.validate viewport = ok (.Ok ()))
    (hmax : self.stamp.revision.val = U64.max) :
    scene.Scene.reject_layout self request viewport =
      ok (.Err topology.Error.Overflow, self) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  rcases u64_checked_succ self.stamp.revision with ⟨hm, hn⟩ | ⟨z, hlt, hz, hs⟩
  · simp [hp, hl, hv, hn, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, lift]
  · omega

theorem reject_layout_scan_failed (self : scene.Scene) (request : Std.U64)
    (viewport : grid.Rect) (hp : self.pending = some request) (hl : self.latest_request = request)
    (hv : grid.Rect.validate viewport = ok (.Ok ()))
    (hlt : self.stamp.revision.val < U64.max) (fits : Bool) (e : topology.Error)
    (hs : rejectScan self viewport = ok (fits, .Err e)) :
    scene.Scene.reject_layout self request viewport = ok (.Err e, self) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  rcases u64_checked_succ self.stamp.revision with ⟨hm, hn⟩ | ⟨z, hlt', hz, hs'⟩
  · omega
  · unfold rejectScan at hs
    have hs2 := hs
    simp only [hp, hl] at hs2
    simp [hp, hl, hv, hs', hs2, lift, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem reject_layout_commit (self : scene.Scene) (request : Std.U64)
    (viewport : grid.Rect) (hp : self.pending = some request) (hl : self.latest_request = request)
    (hv : grid.Rect.validate viewport = ok (.Ok ()))
    (hlt : self.stamp.revision.val < U64.max) (fits : Bool)
    (hs : rejectScan self viewport = ok (fits, .Ok ())) :
    ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
      scene.Scene.reject_layout self request viewport =
        ok (.Ok (bumped self v),
          { self with stamp := bumped self v, inactive := !fits, pending := none }) := by
  unfold scene.Scene.reject_layout
  rw [pending_ne_eval]
  rcases u64_checked_succ self.stamp.revision with ⟨hm, hn⟩ | ⟨z, hlt', hz, hs'⟩
  · omega
  · unfold rejectScan at hs
    have hs2 := hs
    simp only [hp, hl] at hs2
    refine ⟨z, hz, ?_⟩
    simp [hp, hl, hv, hs', hs2, lift, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bumped]

/-! ### `tick` -/

theorem tick_stale_epoch (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h : stamp.epoch ≠ self.stamp.epoch) :
    scene.Scene.tick self stamp wall = ok (.Err topology.Error.StaleEpoch, self) := by
  unfold scene.Scene.tick
  rw [check_stamp_stale_epoch self stamp h]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem tick_stale_revision (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h1 : stamp.epoch = self.stamp.epoch) (h2 : stamp.revision ≠ self.stamp.revision) :
    scene.Scene.tick self stamp wall = ok (.Err topology.Error.StaleRevision, self) := by
  unfold scene.Scene.tick
  rw [check_stamp_stale_revision self stamp h1 h2]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem tick_revision_overflow (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h1 : stamp.epoch = self.stamp.epoch) (h2 : stamp.revision = self.stamp.revision)
    (h3 : self.stamp.revision.val = U64.max) :
    scene.Scene.tick self stamp wall = ok (.Err topology.Error.Overflow, self) := by
  unfold scene.Scene.tick
  rw [check_stamp_overflow self stamp h1 h2 h3]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem tick_wall_regressed (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : wall.val < self.wall.val) :
    scene.Scene.tick self stamp wall = ok (.Err topology.Error.InvalidTransition, self) := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  rw [he]
  have : wall < self.wall := by simpa using hw
  simp [core.result.Result.Insts.CoreOpsTry.branch, this]

theorem tick_frozen (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hfrozen : self.suspended = true ∨ self.inactive = true ∨ self.pending.isSome = true) :
    ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
      scene.Scene.tick self stamp wall =
        ok (.Ok (bumped self v), { self with stamp := bumped self v, wall := wall }) := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  refine ⟨v, hv, ?_⟩
  rw [he]
  have : ¬ wall < self.wall := by simpa using hw
  rcases hfrozen with h | h | h <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch, this, h, bumped, core.option.Option.is_some]

theorem tick_reanchored (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = true) :
    ∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
      scene.Scene.tick self stamp wall =
        ok (.Ok (bumped self v),
          { self with stamp := bumped self v, wall := wall, reanchor := false }) := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  refine ⟨v, hv, ?_⟩
  rw [he]
  have : ¬ wall < self.wall := by simpa using hw
  simp [core.result.Result.Insts.CoreOpsTry.branch, this, hs, hi, hp, hr, bumped,
    core.option.Option.is_some]

theorem tick_clock_overflow (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hov : U64.max < self.clock.val + (wall.val - self.wall.val)) :
    scene.Scene.tick self stamp wall = ok (.Err topology.Error.Overflow, self) := by
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
    simp [lift, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | some z =>
    rw [hco] at hc
    simp at hc
    omega

/-! ### `tick`: the simulation step leaves everything but holds, walkers and patches alone -/

/-- The tuple the generated loops return in place of a scene. -/
def sceneTuple (s : scene.Scene) :=
  (s.layout, s.tree, s.work, s.routes, s.required, s.phases, s.next_phases, s.holds, s.walkers,
    s.patches, s.stamp, s.clock, s.wall, s.reanchor, s.suspended, s.inactive, s.latest_request,
    s.pending, s.trail_revision)

/-- `s` differs from `base` at most in its walkers and patches. -/
def WalkersPatchesOnly (base s : scene.Scene) : Prop :=
  ∃ w p, s = { base with walkers := w, patches := p }

theorem drain_patches_loop0_frame (base : scene.Scene) (x : scene.Scene) (p : Std.Usize)
    (hx : WalkersPatchesOnly base x) :
    lax (scene.Scene.drain_patches_loop0 x p)
      (fun y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }) := by
  unfold scene.Scene.drain_patches_loop0
  refine loop_lax _ (fun x : scene.Scene × Std.Usize => WalkersPatchesOnly base x.1)
    (fun y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }) ?_ (x, p) hx
  rintro ⟨s, p⟩ hs r hr
  simp only at hs hr
  have hl : lax (scene.Scene.drain_patches_loop0.body s p) (fun r =>
      match r with
      | .done y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }
      | .cont x' => WalkersPatchesOnly base x'.1) := by
    unfold scene.Scene.drain_patches_loop0.body
    dsimp only
    split
    · apply lax_bind (lax_triv _); intro p1 _
      apply lax_bind (lax_triv _); intro b _
      split
      · apply lax_bind (lax_triv _); intro crossing _
        split
        · apply lax_bind (lax_triv _); intro p2 _
          exact lax_ok _ hs
        · apply lax_bind (lax_triv _); intro pr _
          obtain ⟨p2, back⟩ := pr
          apply lax_bind (lax_triv _); intro v1 _
          apply lax_bind (lax_triv _); intro p3 _
          obtain ⟨w, q, hs⟩ := hs
          exact lax_ok _ ⟨_, _, by rw [hs]⟩
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
    · obtain ⟨w, q, hs⟩ := hs
      exact lax_ok _ ⟨w, q, by rw [hs]; rfl⟩
  have key := lax_of_ok _ _ r hr hl
  cases r with
  | done y => exact key
  | cont x' => exact key

theorem drain_patches_frame (x : scene.Scene) :
    lax (scene.Scene.drain_patches x) (WalkersPatchesOnly x) := by
  unfold scene.Scene.drain_patches
  apply lax_bind (drain_patches_loop0_frame x x 0#usize ⟨x.walkers, x.patches, rfl⟩)
  rintro y ⟨w, q, rfl⟩
  exact lax_ok _ ⟨w, q, rfl⟩

theorem tick_loop1_frame (base x : scene.Scene) (clock : Std.U64) (p : Std.Usize)
    (hx : WalkersPatchesOnly base x) :
    lax (scene.Scene.tick_loop1 x clock p)
      (fun y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }) := by
  unfold scene.Scene.tick_loop1
  refine loop_lax _ (fun x : scene.Scene × Std.Usize => WalkersPatchesOnly base x.1)
    (fun y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }) ?_ (x, p) hx
  rintro ⟨s, p⟩ hs r hr
  simp only at hs hr
  have hl : lax (scene.Scene.tick_loop1.body clock s p) (fun r =>
      match r with
      | .done y => ∃ w q, y = sceneTuple { base with walkers := w, patches := q }
      | .cont x' => WalkersPatchesOnly base x'.1) := by
    unfold scene.Scene.tick_loop1.body
    dsimp only
    split
    · apply lax_bind (lax_triv _); intro p1 _
      split
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
      · apply lax_bind (lax_triv _); intro p2 _
        exact lax_ok _ hs
      · split
        · apply lax_bind (lax_triv _); intro v _
          apply lax_bind (lax_triv _); intro pr _
          obtain ⟨p2, back⟩ := pr
          apply lax_bind (lax_triv _); intro p3 _
          obtain ⟨w, q, hs⟩ := hs
          exact lax_ok _ ⟨_, _, by rw [hs]⟩
        · apply lax_bind (lax_triv _); intro p2 _
          exact lax_ok _ hs
    · obtain ⟨w, q, hs⟩ := hs
      exact lax_ok _ ⟨w, q, by rw [hs]; rfl⟩
  have key := lax_of_ok _ _ r hr hl
  cases r with
  | done y => exact key
  | cont x' => exact key

theorem tick_active_lax (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max) :
    lax (scene.Scene.tick self stamp wall) (fun res =>
      ∃ (v clock' : Std.U64) (holds' : alloc.vec.Vec Std.Usize)
        (walkers' : alloc.vec.Vec walker.Walker) (patches' : alloc.vec.Vec shatter.Patch),
        v.val = self.stamp.revision.val + 1 ∧
        clock'.val = self.clock.val + (wall.val - self.wall.val) ∧
        res = (.Ok (bumped self v),
          { self with holds := holds', walkers := walkers', patches := patches',
                      stamp := bumped self v, clock := clock', wall := wall })) := by
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
    apply lax_bind (lax_triv _)
    rintro ⟨hold, walk⟩ _
    apply lax_bind (drain_patches_frame _)
    rintro self1 ⟨w1, q1, rfl⟩
    apply lax_bind (tick_loop1_frame _ _ z 0#usize ⟨w1, q1, rfl⟩)
    rintro y ⟨w, q, rfl⟩
    simp only [sceneTuple]
    refine lax_ok _ ⟨v, hv, z, by omega, hold, w, q, ?_⟩
    simp [bumped]

/-- The simulation step on the active path: whenever it returns, only holds, walkers and patches
changed besides the stamp, the clock and the wall timestamp. -/
theorem tick_active (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene)
    (hres : scene.Scene.tick self stamp wall = ok res) :
    ∃ (v clock' : Std.U64) (holds' : alloc.vec.Vec Std.Usize)
      (walkers' : alloc.vec.Vec walker.Walker) (patches' : alloc.vec.Vec shatter.Patch),
      v.val = self.stamp.revision.val + 1 ∧
      clock'.val = self.clock.val + (wall.val - self.wall.val) ∧
      res = (.Ok (bumped self v),
        { self with holds := holds', walkers := walkers', patches := patches',
                    stamp := bumped self v, clock := clock', wall := wall }) :=
  lax_of_ok _ _ res hres (tick_active_lax self stamp wall hacc hw hs hi hp hr hnov)

end Labyrinth
