module
public import LabyrinthCore.ScenePreflight

/-! Scene edits (S3), part 3: `Scene::commit_edit`. It copies the scratch phase table over the
published one, replaces each route's cells when the edit carries routes, stamps the new revision
and, when the edit removes edges, the trail revision. Nothing else changes. These statements do not
reach the geometry, so they are total. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The scene's fields in the order the generated loops return them. -/
def sceneFields (s : scene.Scene) :=
  (s.layout, s.tree, s.work, s.routes, s.required, s.phases, s.next_phases, s.holds, s.walkers,
    s.patches, s.stamp, s.clock, s.wall, s.reanchor, s.suspended, s.inactive, s.latest_request,
    s.pending, s.trail_revision)

/-- The copy loop leaves a phase table equal to the scratch table, from entry `i` on. -/
theorem commit_edit_phase_loop (self : scene.Scene)
    (hn : self.phases.val.length ≤ self.next_phases.val.length) (i : Std.Usize)
    (hi : i.val ≤ self.phases.val.length) :
    scene.Scene.commit_edit_loop0 self i ⦃ out =>
      ∃ ph : alloc.vec.Vec Std.I32, ph.val.length = self.phases.val.length ∧
        (∀ j, j < self.phases.val.length →
          ph.val[j]? = if j < i.val then self.phases.val[j]? else self.next_phases.val[j]?) ∧
        out = sceneFields { self with phases := ph } ⦄ := by
  unfold scene.Scene.commit_edit_loop0
  refine loop.spec_decr_nat (fun x : scene.Scene × Std.Usize =>
      self.phases.val.length - x.2.val)
    (fun x => ∃ ph : alloc.vec.Vec Std.I32, x.1 = { self with phases := ph } ∧
      ph.val.length = self.phases.val.length ∧ x.2.val ≤ self.phases.val.length ∧
      i.val ≤ x.2.val ∧ ∀ j, j < self.phases.val.length →
        ph.val[j]? = if j < i.val ∨ x.2.val ≤ j then self.phases.val[j]?
          else self.next_phases.val[j]?)
    (fun out => ∃ ph : alloc.vec.Vec Std.I32, ph.val.length = self.phases.val.length ∧
        (∀ j, j < self.phases.val.length →
          ph.val[j]? = if j < i.val then self.phases.val[j]? else self.next_phases.val[j]?) ∧
        out = sceneFields { self with phases := ph }) _ _ ?_ ⟨self.phases, by simp, rfl, hi, le_refl _, ?_⟩
  · rintro ⟨s1, i1⟩ ⟨ph, rfl, hlen, hi1, hii, hph⟩
    dsimp only at hlen hi1 hii hph
    unfold scene.Scene.commit_edit_loop0.body
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    by_cases hlt : i1 < alloc.vec.Vec.len ph
    · have hltn : i1.val < self.phases.val.length := by simpa [hlen] using hlt
      simp only [hlt, ite_true]
      apply spec_bind (alloc.vec.Vec.index_usize_spec self.next_phases i1 (by simp; omega))
      intro i2 hi2
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec ph i1 (by simp; omega))
      rintro ⟨x, back⟩ ⟨hx, rfl⟩
      apply spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i3 hi3
      have hi3v : i3.val = i1.val + 1 := by simpa using hi3
      rw [spec_ok]
      dsimp only
      refine ⟨⟨ph.set i1 i2, rfl, by simp [hlen], by omega, by omega, ?_⟩, by omega⟩
      intro j hj
      rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases hji : i1.val = j
      · subst hji
        have : ¬ (i1.val < i.val ∨ i3.val ≤ i1.val) := by omega
        have hl : i1.val < ph.val.length := by omega
        simp only [hl, this, ↓reduceIte, hi2]
        rw [List.getElem?_eq_getElem (by omega)]
      · simp only [hji, ↓reduceIte]
        rw [hph j hj]
        have : (j < i.val ∨ i1.val ≤ j) ↔ (j < i.val ∨ i3.val ≤ j) := by omega
        simp only [this]
    · simp only [hlt, ite_false, spec_ok]
      have hge : i1.val = self.phases.val.length := by
        have : ¬ i1.val < self.phases.val.length := by simpa [hlen] using hlt
        omega
      refine ⟨ph, hlen, fun j hj => ?_, rfl⟩
      rw [hph j hj]
      have : (j < i.val ∨ i1.val ≤ j) ↔ j < i.val := by omega
      simp only [this]
  · intro j hj
    simp [hj]

theorem commit_edit_loop2_eq : scene.Scene.commit_edit_loop2 = scene.Scene.commit_edit_loop0 := rfl

/-- Extending a vector of `usize` by a slice appends the slice, when the length fits. -/
theorem vec_extend_usize (v : alloc.vec.Vec Std.Usize) (s : Slice Std.Usize)
    (h : v.val.length + s.val.length ≤ Std.Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneUsize v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  have hh : v.length + s.length ≤ Std.Usize.max := by simpa using h
  simp only [hh, ↓reduceDIte]
  apply spec_bind (List.clone_spec (clone := core.clone.CloneUsize.clone) (l := s.val) ?_)
  · intro s' hs'
    simp [spec_ok, hs'.1]
  · intro x _
    simp [liftFun1, core.clone.impls.CloneUsize.clone]

/-- The cells a route holds after the edit: the edit's route `j` when it has one, else unchanged. -/
def commitCells (routes : Slice scene.Route) (j : Nat) (old : alloc.vec.Vec Std.Usize) :
    List Std.Usize :=
  match routes.val[j]? with
  | some r => r.cells.val
  | none => old.val

/-- The route loop replaces the cells of routes `i` and on by the edit's, keeping every circle. -/
theorem commit_edit_routes_loop (self : scene.Scene) (routes : Slice scene.Route)
    (hn : routes.val.length ≤ self.routes.val.length) (i : Std.Usize)
    (hi : i.val ≤ routes.val.length) :
    scene.Scene.commit_edit_loop1 self routes i ⦃ s' =>
      ∃ rt : alloc.vec.Vec scene.Route, rt.val.length = self.routes.val.length ∧
        (∀ j r0, self.routes.val[j]? = some r0 → ∃ r1, rt.val[j]? = some r1 ∧
          r1.circle = r0.circle ∧
          r1.cells.val = if i.val ≤ j then commitCells routes j r0.cells else r0.cells.val) ∧
        s' = { self with routes := rt } ⦄ := by
  unfold scene.Scene.commit_edit_loop1
  refine loop.spec_decr_nat (fun x : scene.Scene × Std.Usize => routes.val.length - x.2.val)
    (fun x => ∃ rt : alloc.vec.Vec scene.Route, x.1 = { self with routes := rt } ∧
      rt.val.length = self.routes.val.length ∧ x.2.val ≤ routes.val.length ∧ i.val ≤ x.2.val ∧
      ∀ j r0, self.routes.val[j]? = some r0 → ∃ r1, rt.val[j]? = some r1 ∧
        r1.circle = r0.circle ∧
        r1.cells.val = if i.val ≤ j ∧ j < x.2.val then commitCells routes j r0.cells
          else r0.cells.val)
    (fun s' => ∃ rt : alloc.vec.Vec scene.Route, rt.val.length = self.routes.val.length ∧
        (∀ j r0, self.routes.val[j]? = some r0 → ∃ r1, rt.val[j]? = some r1 ∧
          r1.circle = r0.circle ∧
          r1.cells.val = if i.val ≤ j then commitCells routes j r0.cells else r0.cells.val) ∧
        s' = { self with routes := rt }) _ (self, i) ?_ ⟨self.routes, rfl, rfl, hi, le_refl _, ?_⟩
  · rintro ⟨s1, i1⟩ ⟨rt, rfl, hlen, hi1, hii, hrt⟩
    dsimp only at hlen hi1 hii hrt
    unfold scene.Scene.commit_edit_loop1.body
    simp only [alloc.vec.Vec.index_mut_slice_index]
    by_cases hlt : i1 < Slice.len routes
    · have hltr : i1.val < routes.val.length := hlt
      have hltn : i1.val < rt.val.length := by omega
      simp only [hlt, ite_true]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec rt i1 hltn)
      rintro ⟨r, back⟩ ⟨hr, rfl⟩
      apply spec_bind (vec_clear_spec alloc.alloc.Global r.cells)
      intro v hv
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec
        (rt.set i1 { circle := r.circle, cells := v }) i1 (by simp; omega))
      rintro ⟨r1, back1⟩ ⟨hr1, rfl⟩
      apply spec_bind (Slice.index_usize_spec routes i1 hltr)
      intro r2 hr2
      have hr1' : r1 = { circle := r.circle, cells := v } := by
        rw [hr1]; simp
      subst hr1'
      apply spec_bind (vec_extend_usize v r2.cells.deref (by
        simp only [hv, List.length_nil, zero_add]
        have := r2.cells.deref.property
        omega))
      intro v2 hv2
      apply spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      have hi2v : i2.val = i1.val + 1 := by simpa using hi2
      rw [spec_ok]
      dsimp only
      have hv2c : v2.val = r2.cells.val := by rw [hv2, hv, deref_val]; simp
      refine ⟨⟨(rt.set i1 { circle := r.circle, cells := v }).set i1
          { circle := r.circle, cells := v2 }, rfl, by simp [hlen], by omega, by omega, ?_⟩, by omega⟩
      intro j r0 hj
      obtain ⟨r', hr', hcirc, hcells⟩ := hrt j r0 hj
      simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases hji : i1.val = j
      · subst hji
        have hrr : r = r' := by
          rw [hr]
          have : rt.val[i1.val]? = some rt.val[i1.val] := List.getElem?_eq_getElem hltn
          rw [hr'] at this
          exact (Option.some.inj this).symm
        subst hrr
        refine ⟨{ circle := r.circle, cells := v2 }, ?_, hcirc, ?_⟩
        · simp only [List.length_set]
          simp [hlen]; omega
        · have hgr2 : routes.val[i1.val]? = some r2 := by
            rw [List.getElem?_eq_getElem hltr]; exact congrArg some hr2.symm
          have hcond : i.val ≤ i1.val ∧ i1.val < i2.val := by omega
          simp only [hcond, and_self, ↓reduceIte, hv2c, commitCells, hgr2]
      · refine ⟨r', by simpa [hji] using hr', hcirc, ?_⟩
        rw [hcells]
        have : (i.val ≤ j ∧ j < i1.val) ↔ (i.val ≤ j ∧ j < i2.val) := by omega
        simp only [this]
    · simp only [hlt, ite_false, spec_ok]
      have hge : i1.val = routes.val.length := by
        have : ¬ i1.val < routes.val.length := hlt
        omega
      refine ⟨rt, hlen, fun j r0 hj => ?_, rfl⟩
      obtain ⟨r1, h1, h2, h3⟩ := hrt j r0 hj
      refine ⟨r1, h1, h2, ?_⟩
      rw [h3]
      by_cases hij : i.val ≤ j
      · by_cases hjl : j < i1.val
        · simp [hij, hjl]
        · have : routes.val[j]? = none := by
            rw [List.getElem?_eq_none]; omega
          simp [hij, hjl, commitCells, this]
      · simp [hij]
  · intro j r0 hj
    refine ⟨r0, ?_, rfl, ?_⟩
    · simpa using hj
    · simp

/-- The scene after the edit commits, given the new phase table and routes. -/
def commitResult (self : scene.Scene) (edit : scene.Edit) (revision : Std.U64)
    (ph : alloc.vec.Vec Std.I32) (rt : alloc.vec.Vec scene.Route) : scene.Scene :=
  { self with
    phases := ph
    routes := rt
    stamp := { self.stamp with revision := revision }
    trail_revision := if edit.remove.val.length = 0 then self.trail_revision else revision }

/-- What `commit_edit` does, exactly: the phase table becomes the scratch table, each route's cells
become the edit's (circles kept) when the edit carries routes, the stamp takes the new revision, and
the trail revision does too when the edit removes edges. Nothing else changes. -/
theorem scene_commit_edit_spec (self : scene.Scene) (edit : scene.Edit) (revision : Std.U64)
    (hph : self.phases.val.length ≤ self.next_phases.val.length)
    (hr : ∀ rs, edit.routes = some rs → rs.val.length ≤ self.routes.val.length) :
    scene.Scene.commit_edit self edit revision ⦃ s' =>
      ∃ ph : alloc.vec.Vec Std.I32, ph.val.length = self.phases.val.length ∧
        (∀ j, j < self.phases.val.length → ph.val[j]? = self.next_phases.val[j]?) ∧
      ∃ rt : alloc.vec.Vec scene.Route, rt.val.length = self.routes.val.length ∧
        (∀ j (r0 : scene.Route), self.routes.val[j]? = some r0 → ∃ r1 : scene.Route,
          rt.val[j]? = some r1 ∧
          r1.circle = r0.circle ∧
          r1.cells.val = (match edit.routes with
            | none => r0.cells.val
            | some rs => commitCells rs j r0.cells)) ∧
        s' = commitResult self edit revision ph rt ⦄ := by
  unfold scene.Scene.commit_edit
  cases hre : edit.routes with
  | none =>
    simp only
    apply spec_bind (commit_edit_phase_loop self hph 0#usize (by simp))
    intro out hout
    obtain ⟨ph, hl, hp, rfl⟩ := hout
    simp only [sceneFields]
    apply spec_bind (core.slice.Slice.is_empty_spec edit.remove)
    intro b3 hb3
    by_cases hb : b3 = true
    · simp only [hb, ite_true]
      have h0 : edit.remove.length = 0 := by rw [← hb3]; exact hb
      have h0' : edit.remove.val.length = 0 := by simpa using h0
      rw [spec_ok]
      refine ⟨ph, hl, fun j hj => by simpa using hp j hj, self.routes, rfl,
        fun j r0 hj => ⟨r0, hj, rfl, rfl⟩, ?_⟩
      simp [commitResult, h0']
    · have h0 : ¬ edit.remove.length = 0 := by rw [← hb3]; exact hb
      have h0' : ¬ edit.remove.val.length = 0 := by simpa using h0
      simp only [hb, Bool.false_eq_true, ite_false]
      rw [spec_ok]
      refine ⟨ph, hl, fun j hj => by simpa using hp j hj, self.routes, rfl,
        fun j r0 hj => ⟨r0, hj, rfl, rfl⟩, ?_⟩
      simp [commitResult, h0']
  | some routes =>
    simp only
    apply spec_bind (commit_edit_routes_loop self routes (hr routes hre) 0#usize (by simp))
    intro self1 h1
    obtain ⟨rt, hrl, hrt, rfl⟩ := h1
    rw [commit_edit_loop2_eq]
    apply spec_bind (commit_edit_phase_loop { self with routes := rt } hph 0#usize (by simp))
    intro out hout
    obtain ⟨ph, hl, hp, rfl⟩ := hout
    simp only [sceneFields]
    apply spec_bind (core.slice.Slice.is_empty_spec edit.remove)
    intro b3 hb3
    have hroutes : ∀ j (r0 : scene.Route), self.routes.val[j]? = some r0 → ∃ r1 : scene.Route,
        rt.val[j]? = some r1 ∧ r1.circle = r0.circle ∧
        r1.cells.val = commitCells routes j r0.cells := by
      intro j r0 hj
      obtain ⟨r1, h1, h2, h3⟩ := hrt j r0 hj
      exact ⟨r1, h1, h2, by simpa using h3⟩
    by_cases hb : b3 = true
    · simp only [hb, ite_true]
      have h0 : edit.remove.length = 0 := by rw [← hb3]; exact hb
      have h0' : edit.remove.val.length = 0 := by simpa using h0
      rw [spec_ok]
      refine ⟨ph, hl, fun j hj => by simpa using hp j hj, rt, hrl, hroutes, ?_⟩
      simp [commitResult, h0']
    · have h0 : ¬ edit.remove.length = 0 := by rw [← hb3]; exact hb
      have h0' : ¬ edit.remove.val.length = 0 := by simpa using h0
      simp only [hb, Bool.false_eq_true, ite_false]
      rw [spec_ok]
      refine ⟨ph, hl, fun j hj => by simpa using hp j hj, rt, hrl, hroutes, ?_⟩
      simp [commitResult, h0']

theorem all_edges_of_cells (a b : List scene.Route) (h : a.map (fun r => r.cells.val) =
    b.map (fun r => r.cells.val)) : allEdges a = allEdges b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [allEdges, List.flatMap_cons, h.1] at ih ⊢
      rw [ih ys h.2]

/-- After a committed edit that carries routes, the scene's routes have exactly the edit's cells (the
edit's route list is as long as the scene's); an edit without routes keeps them. -/
theorem scene_commit_edit_routes (self : scene.Scene) (edit : scene.Edit) (revision : Std.U64)
    (hph : self.phases.val.length ≤ self.next_phases.val.length)
    (hlen : ∀ rs, edit.routes = some rs → rs.val.length = self.routes.val.length) :
    scene.Scene.commit_edit self edit revision ⦃ s' =>
      (edit.routes = none → s'.routes = self.routes) ∧
      (∀ rs, edit.routes = some rs → allEdges s'.routes.val = allEdges rs.val) ∧
      s'.tree = self.tree ∧ s'.layout = self.layout ∧ s'.work = self.work ∧
      s'.required = self.required ∧ s'.walkers = self.walkers ∧ s'.holds = self.holds ⦄ := by
  apply spec_mono (scene_commit_edit_spec self edit revision hph (fun rs h => (hlen rs h).le))
  rintro s' ⟨ph, _, _, rt, hrl, hrt, rfl⟩
  refine ⟨fun hn => ?_, fun rs hrs => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [commitResult]
    have hn' : ∀ (j : Nat) (r0 : scene.Route), self.routes.val[j]? = some r0 → ∃ r1 : scene.Route,
        rt.val[j]? = some r1 ∧ r1 = r0 := by
      intro j r0 hj
      obtain ⟨r1, h1, h2, h3⟩ := hrt j r0 hj
      rw [hn] at h3
      refine ⟨r1, h1, ?_⟩
      obtain ⟨c1, v1⟩ := r1
      obtain ⟨c0, v0⟩ := r0
      simp only at h2 h3
      subst h2
      rw [alloc.vec.Vec.ext v1 v0 h3]
    have : rt = self.routes := by
      apply alloc.vec.Vec.ext
      apply List.ext_getElem?
      intro j
      by_cases hj : j < self.routes.val.length
      · have hg : self.routes.val[j]? = some self.routes.val[j] := List.getElem?_eq_getElem hj
        obtain ⟨r1, h1, h2⟩ := hn' j _ hg
        rw [h1, hg, h2]
      · have h1 : self.routes.val[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : rt.val[j]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]
    rw [this]
  · have hl := hlen rs hrs
    simp only [commitResult]
    apply all_edges_of_cells
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
    by_cases hj : j < rs.val.length
    · have hg : self.routes.val[j]? = some self.routes.val[j] := List.getElem?_eq_getElem (by omega)
      obtain ⟨r1, h1, _, h3⟩ := hrt j _ hg
      have hgr : rs.val[j]? = some rs.val[j] := List.getElem?_eq_getElem hj
      rw [h1, hgr]
      simp only [Option.map_some]
      rw [h3]
      simp [hrs, commitCells, hgr]
    · have h1 : rt.val[j]? = none := List.getElem?_eq_none (by omega)
      have h2 : rs.val[j]? = none := List.getElem?_eq_none (by omega)
      rw [h1, h2]

/-- A passing route check means the routes cover every circle. -/
theorem pf_route_call_len (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (h : PfRouteCall self edit req (core.result.Result.Ok ())) :
    (PfRoutes self edit).val.length = self.layout.circles.val.length := by
  unfold PfRouteCall scene.check_routes at h
  by_cases hne : (Slice.len (PfRoutes self edit) != alloc.vec.Vec.len self.layout.circles) = true
  · simp [hne] at h
  · simpa [Slice.len] using hne

end Labyrinth
