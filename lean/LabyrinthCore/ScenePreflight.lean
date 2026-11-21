module
public import LabyrinthCore.ScenePreflightRoutes

/-! Scene edits (S3), part 2: `Scene::preflight_edit`. The error order is: length, removals
(`has_edge`, `doorway`, `Occupied`), `check_routes` against the published tree, the kept tree
edges' doorways, the added edges' doorways. A rejection changes nothing but the scratch list
`required`. Everything here reaches `Layout::doorway`, so the statements are partial correctness
(`OkPost`): they hold of every result the call returns. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem usize_succ_spec (i : Std.Usize) (h : i.val < Std.Usize.max) :
    (i + 1#usize) ⦃ r => r.val = i.val + 1 ⦄ := by
  apply spec_mono (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  intro r hr; simpa using hr

theorem deref_val {α : Type _} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem slice_index_ok {α : Type _} (s : Slice α) (i : Std.Usize) (h : i.val < s.val.length)
    (e : α) (he : Slice.index_usize s i = ok e) : s.val[i.val]? = some e := by
  have hs := Slice.index_usize_spec s i h
  rw [he] at hs
  have := (spec_ok _).mp hs
  rw [List.getElem?_eq_getElem h]
  exact congrArg some this.symm

/-- `check_removal`: an edge that is not a tree edge is `InvalidTransition`; a tree edge goes to the
doorway, whose error is returned as is, and otherwise to the walker scan, which answers
`Occupied` or success. -/
theorem scene_check_removal_spec (self : scene.Scene) (edge : topology.Edge) :
    OkPost (scene.Scene.check_removal self edge) (fun r =>
      (¬ parentEdge (parents self.tree) edge.u.val edge.v.val →
        r = core.result.Result.Err topology.Error.InvalidTransition) ∧
      (parentEdge (parents self.tree) edge.u.val edge.v.val →
        (∃ x, scene.Layout.doorway self.layout edge (alloc.vec.Vec.deref self.phases)
            (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Err x) ∧
          r = core.result.Result.Err x) ∨
        (∃ d b, scene.Layout.doorway self.layout edge (alloc.vec.Vec.deref self.phases)
            (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d) ∧
          scene.Scene.check_removal_loop self.walkers d false 0#usize = ok b ∧
          r = if b then core.result.Result.Err topology.Error.Occupied
              else core.result.Result.Ok ()))) := by
  unfold scene.Scene.check_removal
  refine okPost_bind_eq (okPost_of_spec (mutation_has_edge_total self.tree edge)) ?_
  intro b hbe hb
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro r hr _
    cases r with
    | Err y =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine okPost_ok ⟨fun hn => absurd (hb.mp hbt) hn, fun _ => Or.inl ⟨y, hr, rfl⟩⟩
    | Ok d =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro o ho _
      by_cases hoc : o = true
      · simp only [hoc, ↓reduceIte]
        exact okPost_ok ⟨fun hn => absurd (hb.mp hbt) hn,
          fun _ => Or.inr ⟨d, o, hr, ho, by simp [hoc]⟩⟩
      · simp only [hoc, Bool.false_eq_true, ↓reduceIte]
        exact okPost_ok ⟨fun hn => absurd (hb.mp hbt) hn,
          fun _ => Or.inr ⟨d, o, hr, ho, by simp [hoc]⟩⟩
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok ⟨fun _ => rfl, fun hp => absurd (hb.mpr hp) hbt⟩

/-! ### The removal loop -/

/-- The verdict of the removal check on `remove[j]`. -/
def RemovalVerdict (self : scene.Scene) (remove : Slice topology.Edge) (j : Nat)
    (v : core.result.Result Unit topology.Error) : Prop :=
  ∃ e, remove.val[j]? = some e ∧ ∃ e1, topology.Edge.new e.u e.v = ok e1 ∧
    scene.Scene.check_removal self e1 = ok v

/-- The removal loop reports success after every removal passed, or the first failing removal's
error. -/
def RemovalsPost (self : scene.Scene) (remove : Slice topology.Edge)
    (s : core.result.Result Unit topology.Error) : Prop :=
  (s = core.result.Result.Ok () → ∀ j, j < remove.val.length →
    RemovalVerdict self remove j (core.result.Result.Ok ())) ∧
  ∀ x, s = core.result.Result.Err x → ∃ k, k < remove.val.length ∧
    (∀ j, j < k → RemovalVerdict self remove j (core.result.Result.Ok ())) ∧
    RemovalVerdict self remove k (core.result.Result.Err x)

def RemovalsInv (self : scene.Scene) (remove : Slice topology.Edge)
    (s : (core.result.Result Unit topology.Error) × Std.Usize) : Prop :=
  s.2.val ≤ remove.val.length ∧
  (s.1 = core.result.Result.Ok () → ∀ j, j < s.2.val →
    RemovalVerdict self remove j (core.result.Result.Ok ())) ∧
  ∀ x, s.1 = core.result.Result.Err x → ∃ k, k < s.2.val ∧
    (∀ j, j < k → RemovalVerdict self remove j (core.result.Result.Ok ())) ∧
    RemovalVerdict self remove k (core.result.Result.Err x)

theorem preflight_edit_loop0_body_post (self : scene.Scene) (remove : Slice topology.Edge)
    (status : core.result.Result Unit topology.Error) (i : Std.Usize)
    (hinv : RemovalsInv self remove (status, i)) :
    OkPost (scene.Scene.preflight_edit_loop0.body self remove status i) (fun r =>
      match r with
      | .cont s => RemovalsInv self remove s
      | .done y => RemovalsPost self remove y) := by
  obtain ⟨hi, hok, herr⟩ := hinv
  dsimp only at hi hok herr
  unfold scene.Scene.preflight_edit_loop0.body
  by_cases hlt : i < Slice.len remove
  · have hltNat : i.val < remove.val.length := hlt
    simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec status)) ?_
    intro b hbe hb
    by_cases hbt : b = true
    · have hst : status = core.result.Result.Ok () := by
        cases status with
        | Ok u => rfl
        | Err x => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
      simp only [hbt, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro e he _
      have heGet := slice_index_ok remove i hltNat e he
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro e1 he1 _
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro st1 hst1 _
      have hrv : RemovalVerdict self remove i.val st1 := ⟨e, heGet, e1, he1, hst1⟩
      refine okPost_bind (okPost_of_spec (usize_succ_spec i (by scalar_tac))) ?_
      intro i2 hi2
      refine okPost_ok (show RemovalsInv self remove (st1, i2) from ?_)
      dsimp only [RemovalsInv]
      refine ⟨by omega, fun hst1ok j hj => ?_, fun x hx => ?_⟩
      · by_cases hji : j = i.val
        · subst hji; rw [hst1ok] at hrv; exact hrv
        · exact hok hst j (by omega)
      · refine ⟨i.val, by omega, fun j hj => hok hst j hj, ?_⟩
        rw [hx] at hrv; exact hrv
    · have hst : ∃ x, status = core.result.Result.Err x := by
        cases status with
        | Ok u => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
        | Err x => exact ⟨x, rfl⟩
      simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨x, hx⟩ := hst
      refine okPost_ok ⟨by simp [hx], fun y hy => ?_⟩
      rw [hx] at hy
      obtain ⟨k, hk, h1, h2⟩ := herr x hx
      cases hy
      exact ⟨k, by omega, h1, h2⟩
  · simp only [hlt, ↓reduceIte]
    have hge : i.val = remove.val.length := by
      have : ¬ i.val < remove.val.length := hlt
      omega
    refine okPost_ok ⟨fun hs j hj => hok hs j (by omega), fun x hx => ?_⟩
    obtain ⟨k, hk, h1, h2⟩ := herr x hx
    exact ⟨k, by omega, h1, h2⟩

theorem preflight_edit_loop0_post (self : scene.Scene) (remove : Slice topology.Edge) :
    OkPost (scene.Scene.preflight_edit_loop0 self remove (core.result.Result.Ok ()) 0#usize)
      (RemovalsPost self remove) := by
  unfold scene.Scene.preflight_edit_loop0
  refine okPost_loop (RemovalsInv self remove) (RemovalsPost self remove) _ ?_
    (core.result.Result.Ok (), 0#usize) ⟨by simp, by simp, by simp⟩
  rintro ⟨st, i⟩ h
  dsimp only
  refine okPost_mono (preflight_edit_loop0_body_post self remove st i h) ?_
  intro y hy
  cases y <;> exact hy

/-! ### The added-doorway loop -/

/-- A doorway verdict as a status. -/
def unitOf (r : core.result.Result scene.Doorway topology.Error) :
    core.result.Result Unit topology.Error :=
  match r with
  | .Ok _ => .Ok ()
  | .Err x => .Err x

/-- Success after every index passed, or the first failing index and its error. -/
def FirstFail (n : Nat) (V : Nat → core.result.Result Unit topology.Error → Prop)
    (s : core.result.Result Unit topology.Error) : Prop :=
  (s = core.result.Result.Ok () → ∀ j, j < n → V j (core.result.Result.Ok ())) ∧
  ∀ x, s = core.result.Result.Err x → ∃ k, k < n ∧
    (∀ j, j < k → V j (core.result.Result.Ok ())) ∧ V k (core.result.Result.Err x)

/-- The verdict of the doorway test on `add[j]`. -/
def AddVerdict (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32) (add : Slice topology.Edge)
    (j : Nat) (v : core.result.Result Unit topology.Error) : Prop :=
  ∃ e, add.val[j]? = some e ∧ ∃ e1, topology.Edge.new e.u e.v = ok e1 ∧
    ∃ r, scene.Layout.doorway L e1 (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref next) =
      ok r ∧ v = unitOf r

def AddInv (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32) (add : Slice topology.Edge)
    (s : (core.result.Result Unit topology.Error) × Std.Usize) : Prop :=
  s.2.val ≤ add.val.length ∧
  (s.1 = core.result.Result.Ok () → ∀ j, j < s.2.val →
    AddVerdict L phases next add j (core.result.Result.Ok ())) ∧
  ∀ x, s.1 = core.result.Result.Err x → ∃ k, k < s.2.val ∧
    (∀ j, j < k → AddVerdict L phases next add j (core.result.Result.Ok ())) ∧
    AddVerdict L phases next add k (core.result.Result.Err x)

theorem preflight_edit_loop2_body_post (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32)
    (add : Slice topology.Edge) (status : core.result.Result Unit topology.Error)
    (i : Std.Usize) (hinv : AddInv L phases next add (status, i)) :
    OkPost (scene.Scene.preflight_edit_loop2.body L phases next add status i) (fun r =>
      match r with
      | .cont s => AddInv L phases next add s
      | .done y => FirstFail add.val.length (AddVerdict L phases next add) y) := by
  obtain ⟨hi, hok, herr⟩ := hinv
  dsimp only at hi hok herr
  unfold scene.Scene.preflight_edit_loop2.body
  by_cases hlt : i < Slice.len add
  · have hltNat : i.val < add.val.length := hlt
    simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec status)) ?_
    intro b hbe hb
    by_cases hbt : b = true
    · have hst : status = core.result.Result.Ok () := by
        cases status with
        | Ok u => rfl
        | Err x => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
      simp only [hbt, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro e he _
      have heGet := slice_index_ok add i hltNat e he
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro e1 he1 _
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r hr _
      refine okPost_bind_eq (m := (match r with
          | core.result.Result.Ok _ => ok status
          | core.result.Result.Err error => ok (core.result.Result.Err error)))
        (P := fun s2 => s2 = unitOf r) ?_ ?_
      · subst hst
        cases r <;> exact okPost_ok rfl
      intro st1 _ hst1
      have hrv : AddVerdict L phases next add i.val st1 := ⟨e, heGet, e1, he1, r, hr, hst1⟩
      refine okPost_bind (okPost_of_spec (usize_succ_spec i (by scalar_tac))) ?_
      intro i2 hi2
      refine okPost_ok (show AddInv L phases next add (st1, i2) from ?_)
      dsimp only [AddInv]
      refine ⟨by omega, fun hst1ok j hj => ?_, fun x hx => ?_⟩
      · by_cases hji : j = i.val
        · subst hji; rw [hst1ok] at hrv; exact hrv
        · exact hok hst j (by omega)
      · refine ⟨i.val, by omega, fun j hj => hok hst j hj, ?_⟩
        rw [hx] at hrv; exact hrv
    · have hst : ∃ x, status = core.result.Result.Err x := by
        cases status with
        | Ok u => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
        | Err x => exact ⟨x, rfl⟩
      simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨x, hx⟩ := hst
      refine okPost_ok ⟨by simp [hx], fun y hy => ?_⟩
      rw [hx] at hy
      obtain ⟨k, hk, h1, h2⟩ := herr x hx
      cases hy
      exact ⟨k, by omega, h1, h2⟩
  · simp only [hlt, ↓reduceIte]
    have hge : i.val = add.val.length := by
      have : ¬ i.val < add.val.length := hlt
      omega
    refine okPost_ok ⟨fun hs j hj => hok hs j (by omega), fun x hx => ?_⟩
    obtain ⟨k, hk, h1, h2⟩ := herr x hx
    exact ⟨k, by omega, h1, h2⟩

theorem preflight_edit_loop2_post (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32)
    (add : Slice topology.Edge) :
    OkPost (scene.Scene.preflight_edit_loop2 L phases next add (core.result.Result.Ok ()) 0#usize)
      (FirstFail add.val.length (AddVerdict L phases next add)) := by
  unfold scene.Scene.preflight_edit_loop2
  refine okPost_loop (AddInv L phases next add) (FirstFail add.val.length
    (AddVerdict L phases next add)) _ ?_
    (core.result.Result.Ok (), 0#usize) ⟨by simp, by simp, by simp⟩
  rintro ⟨st, i⟩ h
  dsimp only
  refine okPost_mono (preflight_edit_loop2_body_post L phases next add st i h) ?_
  intro y hy
  cases y <;> exact hy

/-! ### The kept-edge loop -/

/-- The verdict of the kept-edge test on cell `c`: a root cell has no edge, an edge the edit removes
is skipped, any other tree edge must pass the doorway. -/
def KeptVerdict (L : scene.Layout) (t : spanning_tree.Tree) (phases next : alloc.vec.Vec Std.I32)
    (remove : Slice topology.Edge) (c : Nat) (v : core.result.Result Unit topology.Error) : Prop :=
  ∃ p, t.parents.val[c]? = some p ∧
    ((p.val = c ∧ v = core.result.Result.Ok ()) ∨
     (p.val ≠ c ∧ ∃ cu : Std.Usize, cu.val = c ∧ ∃ e, topology.Edge.new cu p = ok e ∧
       ((scene.contains remove e = ok true ∧ v = core.result.Result.Ok ()) ∨
        (scene.contains remove e = ok false ∧ ∃ r,
          scene.Layout.doorway L e (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref next) =
            ok r ∧ v = unitOf r))))

def KeptInv (L : scene.Layout) (t : spanning_tree.Tree) (phases next : alloc.vec.Vec Std.I32)
    (remove : Slice topology.Edge)
    (s : (core.result.Result Unit topology.Error) × Std.Usize × Std.Usize) : Prop :=
  s.2.2.val ≤ t.parents.val.length ∧ s.2.1.val ≤ s.2.2.val ∧
  (s.1 = core.result.Result.Ok () → ∀ j, j < s.2.2.val →
    KeptVerdict L t phases next remove j (core.result.Result.Ok ())) ∧
  ∀ x, s.1 = core.result.Result.Err x → ∃ k, k < s.2.2.val ∧
    (∀ j, j < k → KeptVerdict L t phases next remove j (core.result.Result.Ok ())) ∧
    KeptVerdict L t phases next remove k (core.result.Result.Err x)

theorem preflight_edit_loop1_body_post (L : scene.Layout) (t : spanning_tree.Tree)
    (phases next : alloc.vec.Vec Std.I32) (remove : Slice topology.Edge)
    (status : core.result.Result Unit topology.Error) (moving cell : Std.Usize)
    (hinv : KeptInv L t phases next remove (status, moving, cell)) :
    OkPost (scene.Scene.preflight_edit_loop1.body L t phases next remove status moving cell)
      (fun r => match r with
        | .cont s => KeptInv L t phases next remove s
        | .done y => FirstFail t.parents.val.length (KeptVerdict L t phases next remove) y.1 ∧
            y.2.val ≤ t.parents.val.length) := by
  obtain ⟨hi, hmv, hok, herr⟩ := hinv
  dsimp only at hi hmv hok herr
  unfold scene.Scene.preflight_edit_loop1.body
  simp only [spanning_tree.Tree.impl.parents, Std.bind_ok]
  by_cases hlt : cell < Slice.len (alloc.vec.Vec.deref t.parents)
  · have hltNat : cell.val < t.parents.val.length := by
      simpa [Slice.len, alloc.vec.Vec.deref] using hlt
    simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec status)) ?_
    intro b hbe hb
    by_cases hbt : b = true
    · have hst : status = core.result.Result.Ok () := by
        cases status with
        | Ok u => rfl
        | Err x => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
      simp only [hbt, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro parent hpe _
      have hpGet : t.parents.val[cell.val]? = some parent := by
        have := slice_index_ok (alloc.vec.Vec.deref t.parents) cell
          (by rw [deref_val]; exact hltNat) parent hpe
        rwa [deref_val] at this
      have step : ∀ (st1 : core.result.Result Unit topology.Error) (mv1 c1 : Std.Usize),
          KeptVerdict L t phases next remove cell.val st1 → mv1.val ≤ moving.val + 1 →
          c1.val = cell.val + 1 → KeptInv L t phases next remove (st1, mv1, c1) := by
        intro st1 mv1 c1 hv hm hc
        dsimp only [KeptInv]
        refine ⟨by omega, by omega, fun hst1ok j hj => ?_, fun x hx => ?_⟩
        · by_cases hji : j = cell.val
          · subst hji; rw [hst1ok] at hv; exact hv
          · exact hok hst j (by omega)
        · refine ⟨cell.val, by omega, fun j hj => hok hst j hj, ?_⟩
          rw [hx] at hv; exact hv
      refine okPost_bind (P := fun sm => KeptVerdict L t phases next remove cell.val sm.1 ∧
          sm.2.val ≤ moving.val + 1) ?_ ?_
      swap
      · rintro ⟨st1, mv1⟩ ⟨hv, hm⟩
        dsimp only at hv hm
        refine okPost_bind (okPost_of_spec (usize_succ_spec cell (by scalar_tac))) ?_
        intro c1 hc1
        exact okPost_ok (step _ _ c1 hv hm hc1)
      by_cases hpc : (parent != cell) = true
      · have hpne : parent.val ≠ cell.val := by
          intro h; apply absurd hpc; simp [UScalar.eq_of_val_eq h]
        simp only [hpc, ↓reduceIte]
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro e he _
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro b1 hb1e _
        by_cases hb1 : b1 = true
        · simp only [hb1, ↓reduceIte]
          exact okPost_ok ⟨⟨parent, hpGet, Or.inr ⟨hpne, cell, rfl, e, he,
            Or.inl ⟨by rw [hb1e, hb1], by rw [hst]⟩⟩⟩, by dsimp only; omega⟩
        · have hb1f : b1 = false := by simpa using hb1
          simp only [hb1f, Bool.false_eq_true, ↓reduceIte]
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro r hr _
          refine okPost_bind_eq (m := (match r with
              | core.result.Result.Ok _ => ok status
              | core.result.Result.Err error => ok (core.result.Result.Err error)))
            (P := fun s2 => s2 = unitOf r) ?_ ?_
          · subst hst
            cases r <;> exact okPost_ok rfl
          intro st2 _ hst2
          refine okPost_bind (okPost_trivial _) ?_
          intro lp _
          refine okPost_bind (okPost_trivial _) ?_
          intro p _
          refine okPost_bind (okPost_trivial _) ?_
          intro lp1 _
          refine okPost_bind (okPost_trivial _) ?_
          intro p1 _
          refine okPost_bind (okPost_trivial _) ?_
          intro b2 _
          refine okPost_bind (P := fun i1 => i1.val ≤ moving.val + 1) ?_ ?_
          · by_cases hb2 : b2 = true
            · simp only [hb2, ↓reduceIte]
              apply okPost_of_spec
              apply spec_mono (usize_succ_spec moving (by scalar_tac))
              intro r hr; omega
            · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
              refine okPost_bind (okPost_trivial _) ?_
              intro lp2 _
              refine okPost_bind (okPost_trivial _) ?_
              intro p2 _
              refine okPost_bind (okPost_trivial _) ?_
              intro lp3 _
              refine okPost_bind (okPost_trivial _) ?_
              intro p3 _
              refine okPost_bind (okPost_trivial _) ?_
              intro b3 _
              by_cases hb3 : b3 = true
              · simp only [hb3, ↓reduceIte]
                apply okPost_of_spec
                apply spec_mono (usize_succ_spec moving (by scalar_tac))
                intro r hr; omega
              · simp only [hb3, Bool.false_eq_true, ↓reduceIte]
                exact okPost_ok (by omega)
          · intro i1 hi1
            exact okPost_ok ⟨⟨parent, hpGet, Or.inr ⟨hpne, cell, rfl, e, he,
              Or.inr ⟨by rw [hb1e, hb1f], r, hr, hst2⟩⟩⟩, hi1⟩
      · have hpeq : parent.val = cell.val := by simpa using hpc
        simp only [hpc, Bool.false_eq_true, ↓reduceIte]
        exact okPost_ok ⟨⟨parent, hpGet, Or.inl ⟨hpeq, by rw [hst]⟩⟩, by dsimp only; omega⟩
    · have hst : ∃ x, status = core.result.Result.Err x := by
        cases status with
        | Ok u => simp [core.result.Result.ok?] at hb; simp [hb] at hbt
        | Err x => exact ⟨x, rfl⟩
      simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨x, hx⟩ := hst
      refine okPost_ok ⟨⟨by simp [hx], fun y hy => ?_⟩, by dsimp only; omega⟩
      rw [hx] at hy
      obtain ⟨k, hk, h1, h2⟩ := herr x hx
      cases hy
      exact ⟨k, by omega, h1, h2⟩
  · simp only [hlt, ↓reduceIte]
    have hge : cell.val = t.parents.val.length := by
      have : ¬ cell.val < t.parents.val.length := by simpa [Slice.len, alloc.vec.Vec.deref] using hlt
      omega
    refine okPost_ok ⟨⟨fun hs j hj => hok hs j (by omega), fun x hx => ?_⟩, by dsimp only; omega⟩
    obtain ⟨k, hk, h1, h2⟩ := herr x hx
    exact ⟨k, by omega, h1, h2⟩

theorem preflight_edit_loop1_post (L : scene.Layout) (t : spanning_tree.Tree)
    (phases next : alloc.vec.Vec Std.I32) (remove : Slice topology.Edge) :
    OkPost (scene.Scene.preflight_edit_loop1 L t phases next remove (core.result.Result.Ok ())
        0#usize 0#usize)
      (fun y => FirstFail t.parents.val.length (KeptVerdict L t phases next remove) y.1 ∧
        y.2.val ≤ t.parents.val.length) := by
  unfold scene.Scene.preflight_edit_loop1
  refine okPost_loop (KeptInv L t phases next remove)
    (fun y : (core.result.Result Unit topology.Error) × Std.Usize =>
      FirstFail t.parents.val.length (KeptVerdict L t phases next remove) y.1 ∧
        y.2.val ≤ t.parents.val.length) _ ?_
    (core.result.Result.Ok (), 0#usize, 0#usize) ⟨by simp, by simp, by simp, by simp⟩
  rintro ⟨st, mv, c⟩ h
  dsimp only
  refine okPost_mono (preflight_edit_loop1_body_post L t phases next remove st mv c h) ?_
  intro y hy
  cases y <;> exact hy

theorem preflight_edit_loop2_err (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32)
    (add : Slice topology.Edge) (x : topology.Error) (i : Std.Usize) :
    OkPost (scene.Scene.preflight_edit_loop2 L phases next add (core.result.Result.Err x) i)
      (fun y => y = core.result.Result.Err x) := by
  unfold scene.Scene.preflight_edit_loop2
  refine okPost_loop (fun s : (core.result.Result Unit topology.Error) × Std.Usize =>
    s.1 = core.result.Result.Err x) _ _ ?_ (core.result.Result.Err x, i) rfl
  rintro ⟨st, j⟩ h
  dsimp only at h
  subst h
  unfold scene.Scene.preflight_edit_loop2.body
  by_cases hlt : j < Slice.len add
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec
      (core.result.Result.Err x : core.result.Result Unit topology.Error))) ?_
    intro b _ hb
    have hbf : b = false := by simpa [core.result.Result.ok?] using hb
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok rfl
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok rfl

/-! ### `preflight_edit` -/

/-- The routes `preflight_edit` checks: the edit's own, else the scene's. -/
def PfRoutes (self : scene.Scene) (edit : scene.Edit) : Slice scene.Route :=
  match edit.routes with
  | none => alloc.vec.Vec.deref self.routes
  | some r => r

/-- The route check ran against the published tree with this verdict and left `req` in `required`. -/
def PfRouteCall (self : scene.Scene) (edit : scene.Edit) (req : alloc.vec.Vec topology.Edge)
    (r : core.result.Result Unit topology.Error) : Prop :=
  scene.check_routes self.layout (PfRoutes self edit) (alloc.vec.Vec.deref self.phases)
    (alloc.vec.Vec.deref self.next_phases) (some self.tree) edit self.required = ok (r, req)

/-- The kept tree edges' doorways, then the added edges' doorways, after the route check passed. -/
def PfAfterRoutes (self : scene.Scene) (edit : scene.Edit) (req : alloc.vec.Vec topology.Edge)
    (p : (core.result.Result Std.Usize topology.Error) × scene.Scene) : Prop :=
  (∃ x k, k < self.tree.parents.val.length ∧
    (∀ j, j < k → KeptVerdict self.layout self.tree self.phases self.next_phases edit.remove j
      (core.result.Result.Ok ())) ∧
    KeptVerdict self.layout self.tree self.phases self.next_phases edit.remove k
      (core.result.Result.Err x) ∧
    p = (core.result.Result.Err x, { self with required := req })) ∨
  ((∀ j, j < self.tree.parents.val.length →
      KeptVerdict self.layout self.tree self.phases self.next_phases edit.remove j
        (core.result.Result.Ok ())) ∧
    ((∃ x k, k < edit.add.val.length ∧
        (∀ j, j < k → AddVerdict self.layout self.phases self.next_phases edit.add j
          (core.result.Result.Ok ())) ∧
        AddVerdict self.layout self.phases self.next_phases edit.add k
          (core.result.Result.Err x) ∧
        p = (core.result.Result.Err x, { self with required := req })) ∨
     (∃ moving, moving.val ≤ self.tree.parents.val.length ∧
        (∀ k, k < edit.add.val.length →
          AddVerdict self.layout self.phases self.next_phases edit.add k
            (core.result.Result.Ok ())) ∧
        p = (core.result.Result.Ok moving, { self with required := req }))))

/-- The full outcome of `preflight_edit`, in the order the checks run: length, removals, route
certificate, kept edges, added edges. Only the scratch list `required` ever changes, and only
once the removals have passed. -/
def PreflightOutcome (self : scene.Scene) (edit : scene.Edit)
    (p : (core.result.Result Std.Usize topology.Error) × scene.Scene) : Prop :=
  (edit.remove.val.length ≠ edit.add.val.length ∧
    p = (core.result.Result.Err topology.Error.InvalidTransition, self)) ∨
  (edit.remove.val.length = edit.add.val.length ∧
    ((∃ x k, k < edit.remove.val.length ∧
        (∀ j, j < k → RemovalVerdict self edit.remove j (core.result.Result.Ok ())) ∧
        RemovalVerdict self edit.remove k (core.result.Result.Err x) ∧
        p = (core.result.Result.Err x, self)) ∨
     ((∀ j, j < edit.remove.val.length →
        RemovalVerdict self edit.remove j (core.result.Result.Ok ())) ∧
      ∃ req, (∃ x, PfRouteCall self edit req (core.result.Result.Err x) ∧
          p = (core.result.Result.Err x, { self with required := req })) ∨
        (PfRouteCall self edit req (core.result.Result.Ok ()) ∧ PfAfterRoutes self edit req p))))

theorem scene_preflight_edit_spec (self : scene.Scene) (edit : scene.Edit) :
    OkPost (scene.Scene.preflight_edit self edit) (PreflightOutcome self edit) := by
  unfold scene.Scene.preflight_edit
  by_cases hlen : (Slice.len edit.remove != Slice.len edit.add) = true
  · simp only [hlen, ↓reduceIte]
    refine okPost_ok (Or.inl ⟨?_, rfl⟩)
    intro h
    have : Slice.len edit.remove = Slice.len edit.add :=
      UScalar.eq_of_val_eq (by simpa [Slice.len] using h)
    simp [this] at hlen
  · have heq : edit.remove.val.length = edit.add.val.length := by
      simpa using hlen
    simp only [hlen, Bool.false_eq_true, ↓reduceIte]
    refine okPost_bind (preflight_edit_loop0_post self edit.remove) ?_
    intro status hst0
    cases status with
    | Err x =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      obtain ⟨k, hk, h1, h2⟩ := hst0.2 x rfl
      exact okPost_ok (Or.inr ⟨heq, Or.inl ⟨x, k, hk, h1, h2, rfl⟩⟩)
    | Ok u =>
      cases u
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hrem := hst0.1 rfl
      refine okPost_bind (P := fun vr => PfRouteCall self edit vr.1 vr.2) ?_ ?_
      · cases hr : edit.routes with
        | none =>
          simp only
          refine okPost_bind_eq (okPost_trivial _) ?_
          rintro ⟨r1, v1⟩ hcr _
          exact okPost_ok (by simpa [PfRouteCall, PfRoutes, hr] using hcr)
        | some routes =>
          simp only
          refine okPost_bind_eq (okPost_trivial _) ?_
          rintro ⟨r1, v1⟩ hcr _
          exact okPost_ok (by simpa [PfRouteCall, PfRoutes, hr] using hcr)
      · rintro ⟨v, r⟩ hcall
        dsimp only at hcall
        cases r with
        | Err x =>
          simp
          simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          exact okPost_ok (Or.inr ⟨heq, Or.inr ⟨hrem, v, Or.inl ⟨x, hcall, rfl⟩⟩⟩)
        | Ok u2 =>
          cases u2
          simp
          refine okPost_bind (preflight_edit_loop1_post self.layout self.tree self.phases
            self.next_phases edit.remove) ?_
          rintro ⟨status1, moving⟩ ⟨hk, hmv⟩
          dsimp only at hk hmv
          cases status1 with
          | Err y =>
            refine okPost_bind_eq (preflight_edit_loop2_err self.layout self.phases
              self.next_phases edit.add y 0#usize) ?_
            intro status2 _ hs2
            subst hs2
            simp only [Std.bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok]
            obtain ⟨k, hkl, h1, h2⟩ := hk.2 y rfl
            exact okPost_ok (Or.inr ⟨heq, Or.inr ⟨hrem, v, Or.inr ⟨hcall,
              Or.inl ⟨y, k, hkl, h1, h2, rfl⟩⟩⟩⟩)
          | Ok u3 =>
            cases u3
            have hkept := hk.1 rfl
            refine okPost_bind_eq (preflight_edit_loop2_post self.layout self.phases
              self.next_phases edit.add) ?_
            intro status2 _ hs2
            cases status2 with
            | Err y =>
              simp only [Std.bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok]
              obtain ⟨k, hkl, h1, h2⟩ := hs2.2 y rfl
              exact okPost_ok (Or.inr ⟨heq, Or.inr ⟨hrem, v, Or.inr ⟨hcall,
                Or.inr ⟨hkept, Or.inl ⟨y, k, hkl, h1, h2, rfl⟩⟩⟩⟩⟩)
            | Ok u4 =>
              cases u4
              simp only [Std.bind_ok]
              exact okPost_ok (Or.inr ⟨heq, Or.inr ⟨hrem, v, Or.inr ⟨hcall,
                Or.inr ⟨hkept, Or.inr ⟨moving, hmv, hs2.1 rfl, rfl⟩⟩⟩⟩⟩)

/-- The route check leaves a duplicate-free list inside the carrier's edges, whatever its verdict. -/
theorem pf_route_call_inv (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (r : core.result.Result Unit topology.Error)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required)
    (h : PfRouteCall self edit req r) : RouteInv self.layout.carrier req :=
  (scene_check_routes_required_exact self.layout (PfRoutes self edit)
    (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) (some self.tree)
    edit self.required hc hinv (r, req) h).1

/-- A passing route check certifies every route edge against the edit. -/
theorem pf_route_call_certificate (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required)
    (h : PfRouteCall self edit req (core.result.Result.Ok ())) :
    req.val = foldEdges [] (allEdges (PfRoutes self edit).val) ∧
    ∀ e ∈ allEdges (PfRoutes self edit).val,
      MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val :=
  ⟨(scene_check_routes_required_exact self.layout (PfRoutes self edit)
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) (some self.tree)
      edit self.required hc hinv (core.result.Result.Ok (), req) h).2.1 rfl,
   scene_check_routes_route_certificate self.layout (PfRoutes self edit)
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) self.tree edit
      self.required hc hinv (core.result.Result.Ok (), req) h rfl⟩

/-- A rejected or accepted preflight changes nothing but the scratch list `required`, which keeps its
invariant. -/
theorem scene_preflight_edit_frame (self : scene.Scene) (edit : scene.Edit)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required) :
    OkPost (scene.Scene.preflight_edit self edit) (fun p =>
      ∃ req, p.2 = { self with required := req } ∧ RouteInv self.layout.carrier req) := by
  refine okPost_mono (scene_preflight_edit_spec self edit) ?_
  intro p hp
  have hself : self = { self with required := self.required } := rfl
  rcases hp with ⟨_, rfl⟩ | ⟨_, h | ⟨_, req, h | ⟨hcall, h⟩⟩⟩
  · exact ⟨self.required, hself, hinv⟩
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    exact ⟨self.required, hself, hinv⟩
  · obtain ⟨x, hcall, rfl⟩ := h
    exact ⟨req, rfl, pf_route_call_inv self edit req _ hc hinv hcall⟩
  · refine ⟨req, ?_, pf_route_call_inv self edit req _ hc hinv hcall⟩
    rcases h with ⟨x, k, _, _, _, rfl⟩ | ⟨_, ⟨x, k, _, _, _, rfl⟩ | ⟨mv, _, _, rfl⟩⟩
    · rfl
    · rfl
    · rfl

/-- An accepted preflight: the removals and additions pair up, every route edge of the edit's routes
(else the scene's) is either added by the edit or a tree edge the edit does not remove, and
`required` holds exactly the route edges once each. -/
theorem scene_preflight_edit_accepted (self : scene.Scene) (edit : scene.Edit)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required) :
    OkPost (scene.Scene.preflight_edit self edit) (fun p =>
      ∀ moving, p.1 = core.result.Result.Ok moving →
        edit.remove.val.length = edit.add.val.length ∧
        moving.val ≤ self.tree.parents.val.length ∧
        (∀ j, j < edit.remove.val.length →
          RemovalVerdict self edit.remove j (core.result.Result.Ok ())) ∧
        ∃ req, p.2 = { self with required := req } ∧
          req.val = foldEdges [] (allEdges (PfRoutes self edit).val) ∧
          RouteInv self.layout.carrier req ∧
          ∀ e ∈ allEdges (PfRoutes self edit).val,
            MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val) := by
  refine okPost_mono (scene_preflight_edit_spec self edit) ?_
  intro p hp moving hm
  rcases hp with ⟨_, rfl⟩ | ⟨heq, h | ⟨hrem, req, h | ⟨hcall, h⟩⟩⟩
  · simp at hm
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    simp at hm
  · obtain ⟨x, hcall, rfl⟩ := h
    simp at hm
  · obtain ⟨hfold, hcert⟩ := pf_route_call_certificate self edit req hc hinv hcall
    have hI := pf_route_call_inv self edit req _ hc hinv hcall
    rcases h with ⟨x, k, _, _, _, rfl⟩ | ⟨_, ⟨x, k, _, _, _, rfl⟩ | ⟨mv, hmv, _, rfl⟩⟩
    · simp at hm
    · simp at hm
    · simp only [core.result.Result.Ok.injEq] at hm
      subst hm
      exact ⟨heq, hmv, hrem, req, rfl, hfold, hI, hcert⟩

end Labyrinth
