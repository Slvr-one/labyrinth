module
public import LabyrinthCore.SceneReservation

/-! Reservations (S5), part 2: the holds table. A scene keeps one counter per transform; a crossing
holds the (at most four) transforms its two cells depend on (`walker::Holds`). `Holds::insert`
adds an id once; `acquire_holds` adds one to each held counter when a crossing begins and `tick`
subtracts one from each when it ends. A held id may in principle repeat, so every statement counts
multiplicities (`holdMult`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem array_index_ok {α : Type _} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (h : Std.Array.index_usize v i = ok x) : v.val[i.val]? = some x := by
  unfold Std.Array.index_usize at h
  cases hv : v[i]? with
  | none => rw [hv] at h; simp at h
  | some y =>
    rw [hv] at h
    simp only [ok.injEq] at h
    subst h
    rfl

theorem vec_index_ok {α : Type _} (v : alloc.vec.Vec α) (i : Std.Usize) (x : α)
    (h : alloc.vec.Vec.index_usize v i = ok x) : v.val[i.val]? = some x := by
  unfold alloc.vec.Vec.index_usize at h
  cases hv : v[i.val]? with
  | none => rw [hv] at h; simp at h
  | some y =>
    rw [hv] at h
    simp only [ok.injEq] at h
    subst h
    rfl

theorem usize_add_ok (x y z : Std.Usize) (h : x + y = ok z) : z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  exact this.2.1

theorem usize_sub_ok (x y z : Std.Usize) (h : x - y = ok z) :
    z.val + y.val = x.val ∧ y.val ≤ x.val := by
  have := UScalar.sub_equiv x y
  rw [h] at this
  exact ⟨this.2.1.symm, this.1⟩

theorem u32_add_ok (x y z : Std.U32) (h : x + y = ok z) : z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  exact this.2.1

theorem u32_sub_ok (x y z : Std.U32) (h : x - y = ok z) :
    z.val + y.val = x.val ∧ y.val ≤ x.val := by
  have := UScalar.sub_equiv x y
  rw [h] at this
  exact ⟨this.2.1.symm, this.1⟩

/-- How many of the held ids equal `k`. -/
def holdMult (h : walker.Holds) (k : Nat) : Nat :=
  (h.ids.val.take h.count.val).countP (fun x => decide (x.val = k))

/-- The same, over the first `i` held ids only. -/
def prefMult (h : walker.Holds) (i k : Nat) : Nat :=
  ((h.ids.val.take h.count.val).take i).countP (fun x => decide (x.val = k))

/-- A well-formed holds record names at most four ids, all indices into a table of length `n`. -/
def HoldsIn (h : walker.Holds) (n : Nat) : Prop :=
  h.count.val ≤ 4 ∧ ∀ x ∈ h.ids.val.take h.count.val, x.val < n

theorem holds_ids_length (h : walker.Holds) : h.ids.val.length = 4 := by
  simp

theorem holds_take_length (h : walker.Holds) (hc : h.count.val ≤ 4) :
    (h.ids.val.take h.count.val).length = h.count.val := by
  rw [List.length_take, holds_ids_length]; omega

theorem prefMult_zero (h : walker.Holds) (k : Nat) : prefMult h 0 k = 0 := by
  simp [prefMult]

theorem prefMult_full (h : walker.Holds) (k : Nat) (hc : h.count.val ≤ 4) :
    prefMult h h.count.val k = holdMult h k := by
  simp [prefMult, holdMult, List.take_of_length_le (holds_take_length h hc).le]

theorem prefMult_succ (h : walker.Holds) (i k : Nat)
    (hi : i < h.count.val) (x : Std.Usize) (hx : h.ids.val[i]? = some x) :
    prefMult h (i + 1) k = prefMult h i k + (if x.val = k then 1 else 0) := by
  have hx' : (h.ids.val.take h.count.val)[i]? = some x := by
    rw [List.getElem?_take_of_lt hi]; exact hx
  unfold prefMult
  rw [List.take_add_one, hx']
  simp [List.countP_append, List.countP_cons]

theorem holdMult_ge (h : walker.Holds) (i k : Nat) (hc : h.count.val ≤ 4)
    (hi : i < h.count.val) (x : Std.Usize) (hx : h.ids.val[i]? = some x) (hk : x.val = k) :
    prefMult h i k + 1 ≤ holdMult h k := by
  have := prefMult_succ h i k hi x hx
  simp only [hk, ↓reduceIte] at this
  have hmono : prefMult h (i + 1) k ≤ prefMult h h.count.val k :=
    (List.take_sublist_take_left (by omega)).countP_le
  rw [prefMult_full h k hc] at hmono
  omega

/-! ### Release: the decrement loop of `tick` -/

/-- `w` is `v` with the first `i` held ids' multiplicities subtracted. -/
def SubPref (v w : List Std.Usize) (h : walker.Holds) (i : Nat) : Prop :=
  w.length = v.length ∧ ∀ k, k < v.length → ∃ a b, w[k]? = some a ∧ v[k]? = some b ∧
    a.val + prefMult h i k = b.val

/-- `v` is `w` with the first `i` held ids' multiplicities added. -/
def AddPref (v w : List Std.Usize) (h : walker.Holds) (i : Nat) : Prop :=
  w.length = v.length ∧ ∀ k, k < v.length → ∃ a b, w[k]? = some a ∧ v[k]? = some b ∧
    a.val = b.val + prefMult h i k

/-- Releasing a crossing's holds subtracts each held id's multiplicity from its counter, and does
not fail when the counters cover those multiplicities. -/
theorem release_loop_spec (v : alloc.vec.Vec Std.Usize) (h : walker.Holds)
    (hin : HoldsIn h v.val.length)
    (hcover : ∀ k, k < v.val.length → ∃ b, v.val[k]? = some b ∧ holdMult h k ≤ b.val) :
    ∀ (w : alloc.vec.Vec Std.Usize) (i : Std.Usize), i.val ≤ h.count.val →
      SubPref v.val w.val h i.val →
      scene.Scene.tick_loop0_loop0 w h i ⦃ r => SubPref v.val r.val h h.count.val ⦄ := by
  intro w i hi hsub
  unfold scene.Scene.tick_loop0_loop0
  refine loop.spec_decr_nat (fun x : alloc.vec.Vec Std.Usize × Std.Usize => h.count.val - x.2.val)
    (fun x => x.2.val ≤ h.count.val ∧ SubPref v.val x.1.val h x.2.val)
    (fun r : alloc.vec.Vec Std.Usize => SubPref v.val r.val h h.count.val) _ _ ?_ ⟨hi, hsub⟩
  rintro ⟨w, i⟩ ⟨hi, hsub⟩
  simp only at hi hsub
  unfold scene.Scene.tick_loop0_loop0.body
  by_cases hlt : i < h.count
  · simp only [hlt, ↓reduceIte]
    have hlt' : i.val < h.count.val := hlt
    have hlen4 : i.val < h.ids.length := by
      have := hin.1
      have h4 : h.ids.val.length = 4 := holds_ids_length h
      simp only [Std.Array.length]; omega
    apply spec_bind (Std.Array.index_usize_spec h.ids i hlen4)
    intro x hx
    have hxs : h.ids.val[i.val]? = some x := by
      rw [List.getElem?_eq_getElem (by simpa using hlen4), hx]
    have hxin : x.val < v.val.length := by
      apply hin.2
      have hl := holds_take_length h hin.1
      have : (h.ids.val.take h.count.val)[i.val]? = some x := by
        rw [List.getElem?_take_of_lt hlt']; exact hxs
      exact List.mem_of_getElem? this
    obtain ⟨hwl, hk⟩ := hsub
    have hxw : x.val < w.length := by simpa [alloc.vec.Vec.length, hwl] using hxin
    simp only [alloc.vec.Vec.index_mut_slice_index]
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec w x hxw)
    rintro ⟨a, back⟩ ⟨ha, rfl⟩
    obtain ⟨a', b', ha', hb', hab⟩ := hk x.val hxin
    obtain ⟨b2, hb2, hcov⟩ := hcover x.val hxin
    rw [hb2] at hb'; cases hb'
    have hge := holdMult_ge h i.val x.val hin.1 hlt' x hxs rfl
    have haeq : a = a' := by
      have : w.val[x.val]? = some a := by
        rw [List.getElem?_eq_getElem hxw, ha]
      rw [ha'] at this; exact (Option.some.inj this).symm
    subst haeq
    have hapos : 1 ≤ a.val := by omega
    apply spec_bind (Std.Usize.sub_spec (x := a) (y := 1#usize) (by simpa using hapos))
    intro a1 ha1
    have ha1v : a1.val = a.val - 1 := ha1.1
    apply spec_bind (usize_succ_spec i (by scalar_tac))
    intro i2 hi2
    rw [spec_ok]
    have hi2v : i2.val = i.val + 1 := hi2
    have hsucc := fun k => prefMult_succ h i.val k hlt' x hxs
    refine ⟨⟨by show i2.val ≤ h.count.val; omega, ?_, ?_⟩,
      by show h.count.val - i2.val < h.count.val - i.val; omega⟩
    · simp [alloc.vec.Vec.set_val_eq, hwl]
    · intro k hkv
      obtain ⟨c, d, hc, hd, hcd⟩ := hk k hkv
      rw [hi2v]
      by_cases hkx : x.val = k
      · subst hkx
        have hca : c = a := by
          rw [ha'] at hc; exact (Option.some.inj hc).symm
        subst hca
        refine ⟨a1, d, ?_, hd, ?_⟩
        · simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_self hxw]
        · rw [hsucc]; simp only [↓reduceIte]; omega
      · refine ⟨c, d, ?_, hd, ?_⟩
        · simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_ne hkx]; exact hc
        · rw [hsucc]; simp only [hkx, ↓reduceIte]; omega
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : i.val = h.count.val := by
      have : ¬ i.val < h.count.val := hlt
      omega
    rw [← this]
    exact hsub

theorem slice_index_ok_eq {α : Type _} (s : Slice α) (i : Std.Usize) (x : α)
    (h : Slice.index_usize s i = ok x) : s.val[i.val]? = some x := by
  unfold Slice.index_usize at h
  cases hv : s[i]? with
  | none => rw [hv] at h; simp at h
  | some y =>
    rw [hv] at h
    simp only [ok.injEq] at h
    subst h
    rfl

theorem usize_MAX_val : core.num.Usize.MAX.val = Std.Usize.max := rfl

/-! ### Acquire: the increment loop of `begin_crossing` -/

/-- Acquiring a crossing's holds adds each held id's multiplicity to its counter. -/
theorem acquire_loop_post (v : Slice Std.Usize) (h : walker.Holds) :
    ∀ (s : Slice Std.Usize) (i : Std.Usize), i.val ≤ h.count.val →
      AddPref v.val s.val h i.val →
      OkPost (scene.acquire_holds_loop s h i) (fun r => AddPref v.val r.val h h.count.val) := by
  intro s i hi hadd
  unfold scene.acquire_holds_loop
  refine okPost_loop (fun x : Slice Std.Usize × Std.Usize =>
      x.2.val ≤ h.count.val ∧ AddPref v.val x.1.val h x.2.val)
    (fun r : Slice Std.Usize => AddPref v.val r.val h h.count.val) _ ?_ (s, i) ⟨hi, hadd⟩
  rintro ⟨s, i⟩ ⟨hi, hadd⟩
  simp only at hi hadd
  unfold scene.acquire_holds_loop.body
  by_cases hlt : i < h.count
  · simp only [hlt, ↓reduceIte]
    have hlt' : i.val < h.count.val := hlt
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro x hx _
    have hxs := array_index_ok h.ids i x hx
    have hx4 : i.val < 4 := by
      have := (List.getElem?_eq_some_iff.mp hxs).1
      rw [holds_ids_length] at this; exact this
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro a ha _
    have has := slice_index_ok_eq s x a ha
    have hxl : x.val < s.val.length := (List.getElem?_eq_some_iff.mp has).1
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro a1 ha1 _
    have ha1v : a1.val = a.val + 1 := by simpa using usize_add_ok a 1#usize a1 ha1
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro s' hs' _
    have hspec := Slice.update_spec s x a1 hxl
    rw [hs'] at hspec
    have hs'e : s' = s.set x a1 := (spec_ok s').mp hspec
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro i2 hi2 _
    have hi2v : i2.val = i.val + 1 := by simpa using usize_add_ok i 1#usize i2 hi2
    obtain ⟨hsl, hk⟩ := hadd
    have hsucc := fun k => prefMult_succ h i.val k hlt' x hxs
    have hsv : s'.val = s.val.set x.val a1 := by rw [hs'e]; simp
    refine okPost_ok (show i2.val ≤ h.count.val ∧ AddPref v.val s'.val h i2.val from
      ⟨by omega, ?_, ?_⟩)
    · rw [hsv]; simp [hsl]
    · intro k hkv
      obtain ⟨c, d, hc, hd, hcd⟩ := hk k hkv
      rw [hi2v]
      by_cases hkx : x.val = k
      · subst hkx
        have hca : c = a := by
          rw [has] at hc; exact (Option.some.inj hc).symm
        subst hca
        refine ⟨a1, d, ?_, hd, ?_⟩
        · rw [hsv, List.getElem?_set_self hxl]
        · rw [hsucc]; simp only [↓reduceIte]; omega
      · refine ⟨c, d, ?_, hd, ?_⟩
        · rw [hsv, List.getElem?_set_ne hkx]; exact hc
        · rw [hsucc]; simp only [hkx, ↓reduceIte]; omega
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok ?_
    have : i.val = h.count.val := by
      have : ¬ i.val < h.count.val := hlt
      omega
    rw [← this]
    exact hadd

/-- `begin_crossing` acquires holds by adding the multiplicities. -/
theorem acquire_holds_post (counts : Slice Std.Usize) (h : walker.Holds) :
    OkPost (scene.acquire_holds counts h) (fun r => AddPref counts.val r.val h h.count.val) := by
  unfold scene.acquire_holds
  exact acquire_loop_post counts h counts 0#usize (by simp)
    ⟨rfl, fun k hk => by
      obtain ⟨a, ha⟩ : ∃ a, counts.val[k]? = some a := ⟨_, List.getElem?_eq_getElem hk⟩
      exact ⟨a, a, ha, ha, by simp [prefMult_zero]⟩⟩

/-! ### The capacity check of `begin_crossing` -/

/-- A holds record names valid counters, none of them saturated. -/
def HoldsCapacity (h : walker.Holds) (counts : Slice Std.Usize) : Prop :=
  HoldsIn h counts.val.length ∧
    ∀ x ∈ h.ids.val.take h.count.val, ∀ c, counts.val[x.val]? = some c → c.val < Std.Usize.max

/-- Some held counter is saturated. -/
def HoldsSaturated (h : walker.Holds) (counts : Slice Std.Usize) : Prop :=
  ∃ x ∈ h.ids.val.take h.count.val, ∃ c, counts.val[x.val]? = some c ∧ c.val = Std.Usize.max

theorem check_capacity_loop_post (h : walker.Holds) (counts : Slice Std.Usize) :
    OkPost (scene.check_hold_capacity_loop h counts false 0#usize) (fun o =>
      (o = false → HoldsCapacity h counts) ∧ (o = true → HoldsSaturated h counts)) := by
  unfold scene.check_hold_capacity_loop
  refine okPost_loop (fun x : Bool × Std.Usize =>
      x.2.val ≤ h.count.val ∧ x.2.val ≤ 4 ∧
      (x.1 = false → ∀ y ∈ h.ids.val.take x.2.val, y.val < counts.val.length ∧
        ∀ c, counts.val[y.val]? = some c → c.val < Std.Usize.max) ∧
      (x.1 = true → ∃ y ∈ h.ids.val.take x.2.val, ∃ c, counts.val[y.val]? = some c ∧
        c.val = Std.Usize.max))
    (fun o : Bool => (o = false → HoldsCapacity h counts) ∧ (o = true → HoldsSaturated h counts))
    _ ?_ (false, 0#usize) ⟨by simp, by simp, by simp, by simp⟩
  rintro ⟨o, i⟩ ⟨hi, hi4, hcap, hsat⟩
  simp only at hi hi4 hcap hsat
  unfold scene.check_hold_capacity_loop.body
  by_cases hlt : i < h.count
  · simp only [hlt, ↓reduceIte]
    have hlt' : i.val < h.count.val := hlt
    by_cases ho : o = true
    · simp only [ho, ↓reduceIte]
      refine okPost_ok ⟨fun h0 => by simp at h0, fun _ => ?_⟩
      obtain ⟨y, hy, hyc⟩ := hsat ho
      exact ⟨y, (List.take_sublist_take_left hi).subset hy, hyc⟩
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      have hof : o = false := by simpa using ho
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro x hx _
      have hxs := array_index_ok h.ids i x hx
      have hi4' : i.val < 4 := by
        have := (List.getElem?_eq_some_iff.mp hxs).1
        rw [holds_ids_length] at this; exact this
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro c hc _
      have hcs := slice_index_ok_eq counts x c hc
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro i3 hi3 _
      have hi3v : i3.val = i.val + 1 := by simpa using usize_add_ok i 1#usize i3 hi3
      have hxl : x.val < counts.val.length := (List.getElem?_eq_some_iff.mp hcs).1
      have htk : h.ids.val.take (i.val + 1) = h.ids.val.take i.val ++ [x] := by
        rw [List.take_add_one, hxs]; rfl
      refine okPost_ok (show i3.val ≤ h.count.val ∧ i3.val ≤ 4 ∧ _ ∧ _ from
        ⟨by omega, by omega, ?_, ?_⟩)
      · intro hne y hy
        rw [hi3v, htk] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact (hcap hof) y hy
        · have : y = x := by simpa using hy
          subst this
          refine ⟨hxl, fun c' hc' => ?_⟩
          rw [hcs] at hc'; cases hc'
          have hmax : c.val ≤ Std.Usize.max := by scalar_tac
          have : ¬ (c = core.num.Usize.MAX) := by simpa using hne
          have hne' : c.val ≠ Std.Usize.max := fun h' => this (UScalar.eq_of_val_eq h')
          omega
      · intro heq
        have hceq : c = core.num.Usize.MAX := by simpa using heq
        refine ⟨x, ?_, c, hcs, by rw [hceq]; exact usize_MAX_val⟩
        rw [hi3v, htk]; simp
  · simp only [hlt, ↓reduceIte]
    have hge : i.val = h.count.val := by
      have : ¬ i.val < h.count.val := hlt
      omega
    refine okPost_ok ⟨fun h0 => ?_, fun h1 => ?_⟩
    · have := hcap h0
      rw [hge] at this
      refine ⟨⟨by omega, fun y hy => (this y hy).1⟩, fun y hy => (this y hy).2⟩
    · obtain ⟨y, hy, hyc⟩ := hsat h1
      rw [hge] at hy
      exact ⟨y, hy, hyc⟩

theorem check_hold_capacity_post (h : walker.Holds) (counts : Slice Std.Usize) :
    OkPost (scene.check_hold_capacity h counts) (fun r =>
      (r = core.result.Result.Ok () → HoldsCapacity h counts) ∧
      (r = core.result.Result.Err topology.Error.Overflow → HoldsSaturated h counts) ∧
      (r = core.result.Result.Ok () ∨ r = core.result.Result.Err topology.Error.Overflow)) := by
  unfold scene.check_hold_capacity
  refine okPost_bind (check_capacity_loop_post h counts) ?_
  intro o ho
  by_cases hot : o = true
  · simp only [hot, ↓reduceIte]
    exact okPost_ok ⟨fun h0 => by simp at h0, fun _ => ho.2 hot, Or.inr rfl⟩
  · simp only [hot, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok ⟨fun _ => ho.1 (by simpa using hot), fun h0 => by simp at h0, Or.inl rfl⟩

/-! ### `Holds::insert` -/

theorem holds_insert_loop_spec (self : walker.Holds) (id : Std.Usize) (hc : self.count.val ≤ 4)
    (slot0 : Std.Usize) (h0 : slot0.val ≤ self.count.val) :
    walker.Holds.insert_loop self id slot0 ⦃ r =>
      r.1 = self.ids ∧ r.2.1 = self.count ∧ slot0.val ≤ r.2.2.val ∧
      r.2.2.val ≤ self.count.val ∧
      (∀ j, slot0.val ≤ j → j < r.2.2.val → self.ids.val[j]? ≠ some id) ∧
      (r.2.2.val < self.count.val → self.ids.val[r.2.2.val]? = some id) ⦄ := by
  unfold walker.Holds.insert_loop
  refine loop.spec_decr_nat (fun s : Std.Usize => self.count.val - s.val)
    (fun s => slot0.val ≤ s.val ∧ s.val ≤ self.count.val ∧
      ∀ j, slot0.val ≤ j → j < s.val → self.ids.val[j]? ≠ some id)
    (fun r : (Std.Array Std.Usize 4#usize) × Std.Usize × Std.Usize =>
      r.1 = self.ids ∧ r.2.1 = self.count ∧ slot0.val ≤ r.2.2.val ∧
      r.2.2.val ≤ self.count.val ∧
      (∀ j, slot0.val ≤ j → j < r.2.2.val → self.ids.val[j]? ≠ some id) ∧
      (r.2.2.val < self.count.val → self.ids.val[r.2.2.val]? = some id)) _ _ ?_
    ⟨le_refl _, h0, fun j hj hj' => by omega⟩
  intro slot ⟨hs0, hsc, hno⟩
  unfold walker.Holds.insert_loop.body
  by_cases hlt : slot < self.count
  · simp only [hlt, ↓reduceIte]
    have hlt' : slot.val < self.count.val := hlt
    have hlen4 : slot.val < self.ids.length := by
      have h4 : self.ids.val.length = 4 := holds_ids_length self
      simp only [Std.Array.length]; omega
    apply spec_bind (Std.Array.index_usize_spec self.ids slot hlen4)
    intro x hx
    have hxs : self.ids.val[slot.val]? = some x := by
      rw [List.getElem?_eq_getElem (by simpa using hlen4), hx]
    by_cases hne : x != id
    · simp only [hne, ↓reduceIte]
      apply spec_bind (usize_succ_spec slot (by scalar_tac))
      intro s2 hs2
      rw [spec_ok]
      have hs2v : s2.val = slot.val + 1 := hs2
      have hxid : x ≠ id := by simpa using hne
      refine ⟨⟨by omega, by omega, fun j hj hj' => ?_⟩, by
        show self.count.val - s2.val < self.count.val - slot.val; omega⟩
      by_cases hjs : j = slot.val
      · subst hjs; rw [hxs]; intro h; exact hxid (Option.some.inj h)
      · exact hno j hj (by omega)
    · have hxid : x = id := UScalar.eq_of_val_eq (by simpa using hne)
      simp only [hne, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨trivial, trivial, hs0, hsc, hno, fun _ => by rw [hxs, hxid]⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : slot.val = self.count.val := by
      have : ¬ slot.val < self.count.val := hlt
      omega
    exact ⟨trivial, trivial, hs0, hsc, hno, fun h => by omega⟩

theorem mem_take_iff (h : walker.Holds) (id : Std.Usize) :
    (∃ x ∈ h.ids.val.take h.count.val, x = id) ↔
      ∃ j, j < h.count.val ∧ h.ids.val[j]? = some id := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    have hj' := hj
    rw [List.length_take] at hj'
    refine ⟨j, by omega, ?_⟩
    rw [List.getElem_take] at hjx
    rw [List.getElem?_eq_getElem (by omega), hjx]
  · rintro ⟨j, hj, hjs⟩
    refine ⟨id, ?_, rfl⟩
    apply List.mem_of_getElem? (i := j)
    rw [List.getElem?_take_of_lt hj]; exact hjs

/-- `Holds::insert` adds an id once: an id already held changes nothing; a new id goes into the
next free slot, and a full record rejects it with `InsufficientWorkspace` and stays as it was. -/
theorem holds_insert_spec (self : walker.Holds) (id : Std.Usize) (hc : self.count.val ≤ 4) :
    walker.Holds.insert self id ⦃ r =>
      ((∃ x ∈ self.ids.val.take self.count.val, x = id) →
        r = (core.result.Result.Ok (), self)) ∧
      ((∀ x ∈ self.ids.val.take self.count.val, x ≠ id) → self.count.val = 4 →
        r = (core.result.Result.Err topology.Error.InsufficientWorkspace, self)) ∧
      ((∀ x ∈ self.ids.val.take self.count.val, x ≠ id) → self.count.val < 4 →
        ∃ c' : Std.Usize, c'.val = self.count.val + 1 ∧
          r = (core.result.Result.Ok (),
            ({ ids := self.ids.set self.count id, count := c' } : walker.Holds))) ⦄ := by
  unfold walker.Holds.insert
  apply spec_bind (holds_insert_loop_spec self id hc 0#usize (by simp))
  rintro ⟨a, i, slot⟩ ⟨ha, hi, hlo, hhi, hno, hsome⟩
  simp only at ha hi hlo hhi hno hsome
  subst ha hi
  show (if slot = self.count then _ else _) ⦃ _ ⦄
  by_cases hsl : slot = self.count
  · have hsv : slot.val = self.count.val := by rw [hsl]
    simp only [hsl, ↓reduceIte, lift, bind_ok]
    have hnone : ∀ x ∈ self.ids.val.take self.count.val, x ≠ id := by
      intro x hx hxid
      obtain ⟨j, hj, hjs⟩ := (mem_take_iff self id).mp ⟨x, hx, hxid⟩
      exact hno j (Nat.zero_le _) (by omega) hjs
    have hlen : self.ids.to_slice.len.val = 4 := by simp
    by_cases h4 : self.count.val = 4
    · have hif : self.count = self.ids.to_slice.len := UScalar.eq_of_val_eq (by omega)
      simp only [hif, ↓reduceIte, spec_ok]
      refine ⟨fun hm => ?_, fun _ _ => by rw [← hif], fun _ h => by omega⟩
      rw [← hif] at hm
      obtain ⟨j, hj, hjs⟩ := (mem_take_iff self id).mp hm
      exact absurd hjs (hno j (Nat.zero_le _) (by omega))
    · have hif : ¬ self.count = self.ids.to_slice.len := fun h => h4 (by rw [h]; exact hlen)
      simp only [hif, ↓reduceIte]
      have hlt4 : self.count.val < 4 := by omega
      have hb : self.count.val < self.ids.length := by
        simp only [Std.Array.length]; rw [holds_ids_length]; exact hlt4
      apply spec_bind (Std.Array.update_spec self.ids self.count id hb)
      intro a1 ha1
      apply spec_bind (usize_succ_spec self.count (by scalar_tac))
      intro i2 hi2
      rw [spec_ok]
      refine ⟨fun hm => ?_, fun _ h => by omega, fun _ _ => ⟨i2, hi2, ?_⟩⟩
      · obtain ⟨j, hj, hjs⟩ := (mem_take_iff self id).mp hm
        exact absurd hjs (hno j (Nat.zero_le _) (by omega))
      · rw [ha1]
  · have hsv : slot.val < self.count.val := by
      have : slot.val ≠ self.count.val := fun h => hsl (UScalar.eq_of_val_eq h)
      omega
    simp only [hsl, ↓reduceIte]
    rw [spec_ok]
    have hmem := (mem_take_iff self id).mpr ⟨slot.val, hsv, hsome hsv⟩
    refine ⟨fun _ => rfl, fun hn _ => ?_, fun hn _ => ?_⟩
    · obtain ⟨x, hx, hxid⟩ := hmem; exact absurd hxid (hn x hx)
    · obtain ⟨x, hx, hxid⟩ := hmem; exact absurd hxid (hn x hx)

end Labyrinth
