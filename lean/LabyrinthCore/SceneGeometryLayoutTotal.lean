module
public import LabyrinthCore.SceneGeometryFloor
public import LabyrinthCore.SceneGeometryConnectorTotal
public import LabyrinthCore.SceneGeometryGridTotal
public import LabyrinthCore.SceneGeometryCircleTotal2
public import LabyrinthCore.SceneGeometryEdgesTotal2
public import LabyrinthCore.SceneGeometryEdgesTotal3

/-! Geometry totality (S8), `Layout::new`: the constructor returns for every input. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- An error that came out of `Carrier::from_edges`. -/
def FromEdgesErr (e : topology.Error) : Prop :=
  ∃ n es, topology.Carrier.from_edges n es = ok (.Err e)

/-- The errors `Layout::new` reports. -/
def LayoutNewErr (e : topology.Error) : Prop :=
  e = .InvalidGeometry ∨ e = .InvalidSize ∨ e = .Overflow ∨ e = .InvalidIndex ∨
    e = .InsufficientWorkspace ∨ FromEdgesErr e

/-- What `Layout::new` returns for a layout: the layout invariant, a valid carrier and the
center-radius floor; an error is one of the listed ones. -/
def LayoutNewPost (r : core.result.Result scene.Layout topology.Error) : Prop :=
  (∀ L, r = .Ok L → LayoutGeom L ∧ CarrierValid L.carrier ∧ LayoutFloor L) ∧
  (∀ e, r = .Err e → LayoutNewErr e)

theorem layoutNewPost_err (e : topology.Error) (he : LayoutNewErr e) :
    LayoutNewPost (.Err e) := by
  unfold LayoutNewPost
  exact ⟨fun L h => (by cases h), fun e' h => (by cases h; exact he)⟩

/-- An early return of `Layout::new` through `?`. -/
theorem new_residual (e : topology.Error) (he : LayoutNewErr e) :
    ∃ r, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual scene.Layout
      (core.convert.FromSame topology.Error) (.Err e) = ok r ∧ LayoutNewPost r := by
  refine ⟨.Err e, ?_, layoutNewPost_err e he⟩
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from]

/-- A number of cells the constructor creates, from the inputs alone. -/
def specCells (s : polar.PolarSpec) : Nat := 1 + (s.sectors.val.map (fun x => x.val)).sum

/-- All cells `Layout::new` creates fit in a `usize`: grid cells, circle cells and transitions. -/
def LayoutCapacity (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
    (ps : Slice polar.PortalSpec) : Prop :=
  grid_spec.columns.val * grid_spec.rows.val + (specs.val.map specCells).sum + ps.val.length ≤
    Std.Usize.max

theorem cellsFrom_zero_of_specs (cs : List polar.Circle) (L : List polar.PolarSpec)
    (h : cs.map (·.spec) = L) : cellsFrom cs 0 = (L.map specCells).sum := by
  subst h
  induction cs with
  | nil => simp [cellsFrom]
  | cons c cs ih =>
    simp only [cellsFrom, List.drop_zero, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [circleCells, sectorSum, ringSum, specCells]

/-- The circle loop keeps the specs it consumes: when it ends without an error, the circles carry
exactly the specs of the vector it ran over. -/
theorem layout_new_loop0_specs (specs : alloc.vec.Vec polar.PolarSpec) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    OkPost (scene.Layout.new_loop0 specs margin (alloc.vec.Vec.with_capacity polar.Circle
      (alloc.vec.Vec.len specs)) 0#usize (.Ok ()))
      (fun r => r.2.2 = .Ok () → r.1.val.map (·.spec) = specs.val) := by
  unfold scene.Layout.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error =>
      st.2.2.2 = .Ok () → ∃ pre, specs.val = pre ++ st.1.val ∧ st.2.1.val.map (·.spec) = pre)
    _ _ ?_ (specs, alloc.vec.Vec.with_capacity polar.Circle (alloc.vec.Vec.len specs), 0#usize,
      .Ok ()) (fun _ => ⟨[], by simp, by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]⟩)
  · rintro ⟨it, cs, tr, st⟩ hinv
    simp only at hinv
    unfold scene.Layout.new_loop0.body
    refine okPost_spec (into_iter_next_spec it) ?_
    rintro ⟨o, it1⟩ ⟨hn1, hn2⟩
    cases o with
    | none =>
      refine okPost_ok (fun hst => ?_)
      obtain ⟨pre, h1, h2⟩ := hinv hst
      have hnil : it.val = [] := by
        match h : it.val with
        | [] => rfl
        | hd :: tl => exact absurd (hn2 hd tl h).1 (by simp)
      rw [hnil] at h1
      simp only [List.append_nil] at h1
      rw [h2, h1]
    | some spec =>
    obtain ⟨hd, tl, hit⟩ : ∃ hd tl, it.val = hd :: tl := by
      match h : it.val with
      | [] => exact absurd (hn1 h) (by simp)
      | hd :: tl => exact ⟨hd, tl, rfl⟩
    obtain ⟨h1, h2⟩ := hn2 hd tl hit
    have hhd : hd = spec := by simpa using h1.symm
    subst hhd
    cases st with
    | Err e =>
      refine okPost_spec (core.result.Result.is_ok.step_spec _) ?_
      intro b hb
      cases b with
      | false => exact okPost_ok (fun h => by cases h)
      | true => simp [core.result.Result.is_ok] at hb
    | Ok u =>
    refine okPost_spec (core.result.Result.is_ok.step_spec _) ?_
    intro b hb
    cases b with
    | false => simp [core.result.Result.is_ok] at hb
    | true =>
    refine okPost_bind (okPost_and (circle_new_ok hd 0#usize tr margin hm)
      (circle_new_floor hd 0#usize tr margin hm)) ?_
    intro r hr
    cases r with
    | Err e => exact okPost_ok (fun h => by cases h)
    | Ok circle =>
    obtain ⟨⟨hco, hts, hsp⟩, hfl⟩ : (CircleOk circle (tr.val + hd.sectors.val.length) ∧
        circle.transform_start = tr ∧ circle.spec = hd) ∧ 4 * margin.val ≤ hd.center_radius.val :=
      ⟨hr.1 circle rfl, hr.2 circle rfl⟩
    refine okPost_spec (circle_ring_count_spec circle) ?_
    intro i hi
    simp only [lift, Std.bind_ok]
    rcases hadd : Usize.checked_add tr i with _ | count
    · exact okPost_ok (fun h => by cases h)
    refine okPost_bind (vec_push_okPost cs circle) ?_
    intro cs1 hcs1
    refine okPost_ok ?_
    intro _
    obtain ⟨pre, hpre, hcp⟩ := hinv rfl
    refine ⟨pre ++ [hd], by rw [hpre, hit, h2]; simp, ?_⟩
    simp [hcs1, hcp, hsp]

theorem layout_new_total (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
    (ps : Slice polar.PortalSpec) (geometry : grid.Geometry)
    (hcap : LayoutCapacity grid_spec specs ps) :
    ∃ r, scene.Layout.new grid_spec specs ps geometry = ok r ∧ LayoutNewPost r := by
  unfold scene.Layout.new
  obtain ⟨v, hv, hv1, hv2⟩ := spec_exists_ok (grid_geometry_validate_spec geometry)
  rw [hv]
  cases v with
  | Err e =>
    have := hv2 (by simp)
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    obtain ⟨r, hr, hp⟩ := new_residual e (by
      rcases this with h | h <;> injection h with h <;> subst h <;> simp [LayoutNewErr])
    exact ⟨r, hr, hp⟩
  | Ok u =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have vg2 : MarginOk geometry := (hv1.mp rfl).2.1
  obtain ⟨r1, hr1, hm1, hm2, hm3⟩ := spec_exists_ok (grid_geometry_margin_spec geometry)
  rw [hr1]
  obtain ⟨m, rfl⟩ := hm2 vg2
  obtain ⟨hmg, hmv⟩ := hm1 m rfl
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have hmg' := hmg; unfold MarginOk at hmg'
  have hm : 0 < m.val ∧ m.val ≤ 1000000 := by omega
  obtain ⟨i, hi, hiv⟩ : ∃ i, m * 2#i32 = ok i ∧ i.val = m.val * 2 := by
    have := I32.mul_spec (x := m) (y := 2#i32) (by scalar_tac) (by scalar_tac)
    obtain ⟨i, hi, hv⟩ := spec_exists_ok this
    exact ⟨i, hi, by simpa using hv⟩
  rw [hi]; simp only [Std.bind_ok, uncurry_apply_pair]
  by_cases hcs : grid_spec.cell_size < i
  · simp only [hcs, ↓reduceIte]
    exact ⟨_, rfl, layoutNewPost_err _ (by simp [LayoutNewErr])⟩
  simp only [hcs, ↓reduceIte]
  obtain ⟨r2, hr2, hg1, hg2, hg3⟩ := spec_exists_ok (grid_grid_new_spec grid_spec)
  rw [hr2]
  cases r2 with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact new_residual e (by rcases hg3 e rfl with h | h | h <;> subst h <;> simp [LayoutNewErr])
  | Ok val1 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  obtain ⟨hgs, hgo, hfar1, hfar2⟩ := hg1 val1 rfl
  rw [constructor_check_storage_eq]
  simp only [Std.bind_ok, uncurry_apply_pair]
  by_cases hf1 : constructorStorageFits (alloc.vec.Vec.len specs) 128#usize
  swap
  · simp only [hf1, ↓reduceIte, branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact new_residual _ (by simp [LayoutNewErr])
  simp only [hf1, ↓reduceIte, branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  rw [constructor_check_storage_eq]
  simp only [Std.bind_ok, uncurry_apply_pair]
  by_cases hf2 : constructorStorageFits (Slice.len ps) 56#usize
  swap
  · simp only [hf2, ↓reduceIte, branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact new_residual _ (by simp [LayoutNewErr])
  simp only [hf2, ↓reduceIte, branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  simp only [alloc.vec.IntoIteratorVec.into_iter, Std.bind_ok, bind_tc_ok]
  have hspl : specs.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨⟨circles1, transforms, status⟩, hl0, hl0s⟩ := layout_new_loop0_total specs m
    (alloc.vec.Vec.with_capacity polar.Circle (alloc.vec.Vec.len specs)) 0#usize (.Ok ()) hm
    (by have := hspl; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, this])
  erw [Std.bind_ok]
  rw [hl0]; simp only [Std.bind_ok, uncurry_apply_pair]
  have hinv0 : CirclesOk (alloc.vec.Vec.with_capacity polar.Circle (alloc.vec.Vec.len specs)).val 0 :=
    fun i h => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at h
  have hq0 := layout_new_loop0_ok specs m _ 0#usize (.Ok ()) hm hinv0 _ hl0
  have hf0 := layout_new_loop0_floor specs m _ 0#usize (.Ok ()) hm
    (fun c hc => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at hc) _ hl0
  have hrs0 := layout_new_loop0_ring_starts specs m _ 0#usize (.Ok ()) hm
    (fun c hc => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at hc) _ hl0
  have hsp0 := layout_new_loop0_specs specs m hm _ hl0
  have hl0s' := hl0s circle_status_ok
  cases status with
  | Err e =>
    obtain ⟨r, hr, hp⟩ := new_residual e (by
      rcases hl0s' e rfl with h | h | h <;> subst h <;> simp [LayoutNewErr])
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact ⟨r, hr, hp⟩
  | Ok u5 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have hsp := hsp0 rfl
  obtain ⟨bands, hb, hbv, hbl⟩ := spec_exists_ok
    (alloc.vec.from_elem_spec core.clone.CloneI32 0#i32 circles1.len rfl)
  rw [hb]; simp only [Std.bind_ok, uncurry_apply_pair]
  obtain ⟨counts, hcn, hcv, hcl⟩ := spec_exists_ok
    (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize circles1.len rfl)
  rw [hcn]; simp only [Std.bind_ok, uncurry_apply_pair]
  have hb0 : BandsOk bands.val circles1.val.length := by
    refine ⟨by simp [hbv], fun k hk => ?_⟩
    simp [hbv]
  have hcl' : counts.val.length = circles1.val.length := by simp [hcv]
  have hcnt : ∀ k (h : k < counts.val.length), (counts.val[k]'h).val ≤ (0#usize).val := by
    intro k h; simp [hcv]
  obtain ⟨⟨status1, bands1, counts1⟩, hl1, hl1a, hl1b, he1⟩ :=
    layout_new_loop1_total ps m circles1 (.Ok ()) bands counts 0#usize hm hb0 hcl' hcnt
  have hq1 := layout_new_loop1_ok ps m circles1 (.Ok ()) bands counts 0#usize hm hb0
    (fun _ j _ hj => by simp at hj) _ hl1
  simp only at hq1 hl1a hl1b
  have he1 := he1 rfl
  rw [hl1]; simp only [Std.bind_ok, uncurry_apply_pair]
  cases status1 with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact new_residual e (by have := he1 e rfl; subst this; simp [LayoutNewErr])
  | Ok u6 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have hp1 := hq1.2 rfl
  have hext0 : ExtentOk circles1.val bands1.val 0 := fun j h1 h2 hj => absurd hj (Nat.not_lt_zero _)
  obtain ⟨status2, hl2, he2⟩ := layout_new_loop2_total m circles1 (.Ok ()) bands1 counts1 0#usize
    transforms.val hq0 hq1.1 hl1b hm (fun _ => hext0)
  have hq2 := layout_new_loop2_ok m circles1 (.Ok ()) bands1 counts1 0#usize hq1.1.1
    (fun _ => hext0) _ hl2
  have he2 := he2 rfl
  rw [hl2]; simp only [Std.bind_ok, uncurry_apply_pair]
  cases status2 with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact new_residual e (by rcases he2 e rfl with h | h <;> subst h <;> simp [LayoutNewErr])
  | Ok u7 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have hext := hq2 rfl
  -- loop 3: grid cells
  have hgs : val1.spec = grid_spec := hgs
  have hn : grid_spec.columns = val1.spec.columns := by rw [hgs]
  have hn1 : grid_spec.rows = val1.spec.rows := by rw [hgs]
  obtain ⟨⟨cell_grid, cells⟩, hl3, hl3a, hl3b, hl3c, hl3d⟩ := spec_exists_ok
    (layout_new_loop3_total_new grid_spec.columns grid_spec.rows geometry val1 circles1 bands1
      hgo hn hn1 hq0 hq1.1 hext)
  simp only at hl3a hl3b hl3c hl3d
  have hix := layout_new_loop3_idx grid_spec.columns grid_spec.rows geometry val1 circles1 bands1
    (alloc.vec.Vec.new scene.Cell) 0#usize (fun c hc => by simp [alloc.vec.Vec.new] at hc) _ hl3
  have hcells3 := layout_new_loop3_ok grid_spec.columns grid_spec.rows geometry val1 circles1 bands1
    (alloc.vec.Vec.new scene.Cell) 0#usize (fun c hc => by simp [alloc.vec.Vec.new] at hc) _ hl3
  rw [hl3]; simp only [Std.bind_ok, uncurry_apply_pair]
  -- loop 4: center and sector cells
  have hcf := cellsFrom_zero_of_specs circles1.val specs.val hsp
  have hcap4 : cells.val.length + cellsFrom circles1.val (0#usize).val ≤ Std.Usize.max := by
    have h0 : (0#usize).val = 0 := rfl
    rw [h0, hcf]
    have h1 := hl3d
    have h2 := hcap
    unfold LayoutCapacity at h2
    omega
  obtain ⟨⟨circles2, cells1⟩, hl4, hk4, hpl4, hlen4, k4, hk4eq, hgf4⟩ := spec_exists_ok
    (layout_new_loop4_total circles1 cells 0#usize hrs0 hcap4)
  simp only at hk4 hpl4 hlen4 hk4eq hgf4
  have hq4 := layout_new_loop4_ok circles1 cells 0#usize (circles1.val.map circleKey) rfl
    (fun c hc => by obtain ⟨a, b, r, rfl, hr⟩ := hl3c c hc; exact hr) _ hl4
  simp only at hq4
  rw [hl4]; simp only [Std.bind_ok, uncurry_apply_pair]
  have hlen2 : circles2.val.length = circles1.val.length := by
    have := congrArg List.length hk4; simpa using this
  -- loop 5: portals
  have hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o :=
    fun c r => grid_grid_cell_total cell_grid hl3a c r
  have hcap5 : cells1.val.length + (ps.val.length - (0#usize).val) ≤ Std.Usize.max := by
    have h0 : (0#usize).val = 0 := rfl
    rw [h0]
    have h1 := hl3d
    have h2 := hcap
    unfold LayoutCapacity at h2
    rw [h0] at hlen4
    omega
  have hps : ∀ j (h : j < ps.val.length),
      PortalSpecOk ((circles1.val.map circleKey).map (·.1)).length (ps.val[j]'h) :=
    fun j h => by simpa using hp1 j h
  have hinv5 : PortalLoopInv ((circles1.val.map circleKey).map (·.1)) ps (.Ok u7) cells1
      (alloc.vec.Vec.with_capacity scene.Portal ps.len) (0#usize).val :=
    ⟨fun _ => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new],
     fun j h => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at h,
     fun c hc => by simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hq4.2 c hc⟩
  obtain ⟨⟨status3, cells2, portals1⟩, hl5, hl5a, hl5b, ⟨k5, hk5eq, hgf5⟩, hstat5⟩ := spec_exists_ok
    (layout_new_loop5_total ps cell_grid (.Ok u7) cells1
      (alloc.vec.Vec.with_capacity scene.Portal ps.len) 0#usize
      ((circles1.val.map circleKey).map (·.1)) hps hinv5 hcell hcap5)
  simp only at hl5a hl5b
  have hq5 := layout_new_loop5_ok ps cell_grid (.Ok u7) cells1
    (alloc.vec.Vec.with_capacity scene.Portal ps.len) 0#usize
    ((circles1.val.map circleKey).map (·.1)) hps hinv5 _ hl5
  have he5 := hstat5 rfl
  simp only at hq5
  rw [hl5]; simp only [Std.bind_ok, uncurry_apply_pair]
  cases status3 with
  | Err e =>
    obtain ⟨r, hr, hp⟩ := new_residual e (by have := he5 e rfl; subst this; simp [LayoutNewErr])
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact ⟨r, hr, hp⟩
  | Ok u8 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  simp only [alloc.vec.Vec.is_empty, Std.bind_ok]
  by_cases hemp : alloc.vec.Vec.length cells2 = 0
  · simp only [hemp, decide_true, ↓reduceIte]
    exact ⟨_, rfl, layoutNewPost_err _ (by simp [LayoutNewErr])⟩
  simp only [hemp, decide_false, Bool.false_eq_true, ↓reduceIte]
  rcases usize_checked_mul_cases cells2.len cells2.len with ⟨hmn, hmx⟩ | ⟨z, hz, hzv, hzle⟩
  · simp only [lift, hmn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact new_residual _ (by simp [LayoutNewErr])
  simp only [lift, hz, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  have hc : cells2.val.length * cells2.val.length ≤ Std.Usize.max := by
    have : cells2.len.val = cells2.val.length := by simp [alloc.vec.Vec.len]
    rw [this] at hzle; exact hzle
  have h0 : (0#usize).val = 0 := rfl
  have hlen_ext : cells2.val.length = cells1.val.length + k5.length := by rw [hk5eq]; simp
  have hP0 : (alloc.vec.Vec.with_capacity scene.Portal ps.len).val.length = 0 := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  have hsum : sectorsFrom circles2.val 0 + portals1.val.length ≤ cells2.val.length := by
    refine edges_sum_bound circles1.val circles2.val cells.val.length cells1.val.length
      cells2.val.length portals1.val.length hk4 ?_ ?_
    · rw [h0] at hlen4; exact hlen4
    · omega
  have hcs : CirclesOk circles2.val transforms.val := circlesOk_of_keys hk4.symm hq0
  have hpl : ∀ c ∈ circles2.val, Placed cells2.val.length c := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    exact (hpl4 j hj (by omega)).mono (by omega)
  have hpc : ∀ p ∈ portals1.val, p.spec.circle.val < circles2.val.length := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := hl5b p hp
    have := (hp1 j hj).1
    rw [hpj, hlen2]; exact this
  have hg : GridIdx cells2.val Std.Usize.max Std.Usize.max := by
    have h1 : GridIdx cells.val Std.Usize.max Std.Usize.max := by
      intro c hc a b d h
      obtain ⟨x, y⟩ := hix c hc a b d h
      have := grid_spec.columns.hBounds; have := grid_spec.rows.hBounds
      constructor <;> scalar_tac
    have h2 := GridIdx.append h1 hgf4
    rw [← hk4eq] at h2
    have h3 := GridIdx.append h2 hgf5
    rwa [← hk5eq] at h3
  obtain ⟨e1, e2, e3, he1, he2, he3, hlen3⟩ := layout_new_edges_total cell_grid cells2 circles2
    portals1 transforms.val hc hcell hg hcs hpl hpc hsum
  rw [he1]; simp only [Std.bind_ok]
  rw [he2]; simp only [Std.bind_ok]
  rw [he3]; simp only [Std.bind_ok]
  obtain ⟨r6, hr6, hr6p⟩ := spec_exists_ok
    (constructor_carrier_from_edges_total_spec cells2.len (alloc.vec.Vec.deref e3))
  rw [hr6]; simp only [Std.bind_ok]
  cases r6 with
  | Err e =>
    obtain ⟨r, hr, hp⟩ := new_residual e (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨_, _, hr6⟩)))))
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact ⟨r, hr, hp⟩
  | Ok carrier =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  have hcar : CarrierValid carrier := hr6p
  obtain ⟨zero, hz, hzv, hzl⟩ := spec_exists_ok
    (alloc.vec.from_elem_spec core.clone.CloneI32 0#i32 transforms rfl)
  rw [hz]; simp only [Std.bind_ok]
  let L : scene.Layout :=
    { cell_grid := cell_grid
      cells := cells2
      circles := circles2
      portals := portals1
      bands := bands1
      geometry := geometry
      carrier := carrier
      transforms := transforms }
  have hspecs := specs_of_keys hk4
  have hLgeom : LayoutGeom L := by
    refine ⟨vg2, fun i h => ?_, by simp [L, hq1.1.1, hlen2], fun i h h2 => ?_, fun i h => ?_⟩
    · have hi1 : i < circles1.val.length := by simp only [L] at h; omega
      have hkey := keys_get hk4 i h hi1
      simp only [circleKey, Prod.mk.injEq] at hkey
      exact (hq0 i hi1).congr hkey.1 hkey.2.1 hkey.2.2
    · have hi1 : i < circles1.val.length := by simp only [L] at h2; omega
      have hkey := keys_get hk4 i h2 hi1
      simp only [circleKey, Prod.mk.injEq] at hkey
      refine ⟨hq1.1.2 i h, ?_⟩
      show (circles2.val[i]'h2).outer.val + (bands1.val[i]'h).val ≤ 1000000
      rw [hkey.2.1]
      exact hext i hi1 h hi1
    · apply cellOkS_cellOk
      show CellOkS (circles2.val.map (·.spec)) portals1.val _
      rw [hspecs]
      exact hq5 _ (List.getElem_mem h)
  have hfloor : LayoutFloor L := by
    intro i h
    have hi1 : i < circles1.val.length := by simp only [L] at h; omega
    have hkey := keys_get hk4 i h hi1
    simp only [circleKey, Prod.mk.injEq] at hkey
    show 4 * layoutMargin geometry ≤ (circles2.val[i]'h).spec.center_radius.val
    rw [hkey.1]
    have := hf0 _ (List.getElem_mem hi1)
    unfold layoutMargin; omega
  have hcirc9 : ∀ j (h : j < L.portals.val.length),
      (L.portals.val[j]'h).spec.circle.val < L.circles.val.length :=
    fun j h => hpc _ (List.getElem_mem h)
  obtain ⟨status4, hl9, hl9s⟩ := layout_new_loop9_total L hLgeom hcar zero
    (by simp [L, hzv, hzl]) hcirc9 (.Ok u8) connectorStatusOk_ok 0#usize (by simp)
  rw [hl9]; simp only [Std.bind_ok]
  cases status4 with
  | Err e =>
    obtain ⟨r, hr, hp⟩ := new_residual e (by
      rcases hl9s e rfl with h | h | h <;> subst h <;> simp [LayoutNewErr])
    simp only [branch_err_eq, Std.bind_ok, uncurry_apply_pair]
    exact ⟨r, hr, hp⟩
  | Ok u10 =>
  simp only [branch_ok_eq, Std.bind_ok, uncurry_apply_pair]
  refine ⟨.Ok L, rfl, ?_⟩
  unfold LayoutNewPost
  exact ⟨fun L' h => by cases h; exact ⟨hLgeom, hcar, hfloor⟩, fun e h => by cases h⟩

/-- Every layout `Layout::new` accepts satisfies the invariant, has a valid carrier and keeps the
center-radius floor. -/
theorem layout_new_ok_post (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
    (ps : Slice polar.PortalSpec) (geometry : grid.Geometry)
    (hcap : LayoutCapacity grid_spec specs ps) (L : scene.Layout)
    (hnew : scene.Layout.new grid_spec specs ps geometry = ok (.Ok L)) :
    LayoutGeom L ∧ CarrierValid L.carrier ∧ LayoutFloor L := by
  obtain ⟨r, hr, hp⟩ := layout_new_total grid_spec specs ps geometry hcap
  rw [hnew] at hr
  have : r = .Ok L := by
    simp at hr
    exact hr.symm
  subst this
  exact hp.1 L rfl

/-- In a layout `Layout::new` accepts, the narrowing of the doorway's angular minimum is exact. -/
theorem layout_new_doorway_minimum_exact (grid_spec : grid.GridSpec)
    (specs : alloc.vec.Vec polar.PolarSpec) (ps : Slice polar.PortalSpec)
    (geometry : grid.Geometry) (hcap : LayoutCapacity grid_spec specs ps) (L : scene.Layout)
    (hnew : scene.Layout.new grid_spec specs ps geometry = ok (.Ok L))
    (m : Std.I32) (hmv : m.val = layoutMargin L.geometry) (circle : Std.Usize)
    (hcl : circle.val < L.circles.val.length) (from_radius to_radius : Std.I32)
    (hf : 0 ≤ from_radius.val ∧ from_radius.val ≤ 1000000)
    (ht : 0 ≤ to_radius.val ∧ to_radius.val ≤ 1000000) :
    (do
      let i2 ← lift (core.cmp.impls.OrdI32.min from_radius to_radius)
      let radius ← lift (core.cmp.impls.OrdI32.max i2 (L.circles.val[circle.val]'hcl).spec.center_radius)
      let i3 ← lift (core.convert.num.FromI64I32.from m)
      let i4 ← i3 * 2#i64
      let i5 ← lift (core.convert.num.FromI64I32.from polar.TURN)
      let i6 ← i4 * i5
      let i7 ← lift (core.convert.num.FromI64I32.from radius)
      let i8 ← i6 + i7
      let i9 ← i8 - 1#i64
      let i10 ← lift (core.convert.num.FromI64I32.from radius)
      let i11 ← i9 / i10
      lift (IScalar.cast .I32 i11)) ⦃ minimum =>
      ∃ radius : Int, 4 * m.val ≤ radius ∧ radius ≤ 1000000 ∧
        minimum.val = (2 * m.val * 4096 + radius - 1) / radius ∧
        1 ≤ minimum.val ∧ minimum.val ≤ 2048 ⦄ := by
  obtain ⟨hg, hc, hf'⟩ := layout_new_ok_post grid_spec specs ps geometry hcap L hnew
  exact layout_doorway_minimum_exact L hg hf' m hmv circle hcl from_radius to_radius hf ht

end Labyrinth
