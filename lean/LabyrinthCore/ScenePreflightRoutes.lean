module
public import LabyrinthCore.SceneConstructionRequired
public import LabyrinthCore.MutationEditEdges
public import LabyrinthCore.MutationPreflight

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem exists_idx_iff_mem {α : Type _} (l : List α) (P : α → Prop) :
    (∃ j, j < l.length ∧ ∃ x, l[j]? = some x ∧ P x) ↔ ∃ x ∈ l, P x := by
  constructor
  · rintro ⟨j, hj, x, hx, hp⟩
    exact ⟨x, List.mem_of_getElem? hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    exact ⟨j, hj, x, by simp [hj, hget], hp⟩

theorem scene_contains_spec (edges : Slice topology.Edge) (edge : topology.Edge) :
    scene.contains edges edge ⦃ b =>
      (b = true ↔ ∃ x ∈ edges.val, mutationCanonicalEdge x = edge) ⦄ := by
  unfold scene.contains scene.contains_loop
  apply loop.spec_decr_nat
    (fun s : Bool × Usize => edges.val.length - s.2.val)
    (fun s : Bool × Usize => s.2.val ≤ edges.val.length ∧
      (s.1 = true ↔ ∃ j, j < s.2.val ∧ ∃ x, edges.val[j]? = some x ∧
        mutationCanonicalEdge x = edge))
    _
  · rintro ⟨found, i⟩ ⟨hi, hfound⟩
    dsimp only at hi hfound
    unfold scene.contains_loop.body
    by_cases hlt : i < Slice.len edges
    · have hltNat : i.val < edges.val.length := hlt
      simp only [hlt, ite_true]
      by_cases hf : found = true
      · simp only [hf, ite_true, spec_ok]
        have := hfound.mp hf
        obtain ⟨j, hj, x, hx, hp⟩ := this
        exact iff_of_true trivial ((exists_idx_iff_mem edges.val
          (fun x => mutationCanonicalEdge x = edge)).mp ⟨j, by omega, x, hx, hp⟩)
      · simp only [hf, Bool.false_eq_true, ite_false]
        apply spec_bind (Slice.index_usize_spec edges i hltNat)
        intro e he
        have heGet : edges.val[i.val]? = some e := by
          rw [List.getElem?_eq_getElem hltNat]
          exact congrArg some he.symm
        apply spec_bind (mutation_edge_new_total e.u e.v)
        intro c hc
        have hcEq : c = mutationCanonicalEdge e := hc
        apply spec_bind (edge_eq_spec c edge)
        intro r hr
        apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        have hi2v : i2.val = i.val + 1 := by simpa using hi2
        simp only [spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hr, hcEq]
        constructor
        · intro h
          exact ⟨i.val, by omega, e, heGet, h⟩
        · rintro ⟨j, hj, x, hx, hp⟩
          by_cases hji : j = i.val
          · rw [hji, heGet] at hx
            cases hx
            exact hp
          · exfalso
            exact hf (hfound.mpr ⟨j, by omega, x, hx, hp⟩)
    · simp only [hlt, ite_false, spec_ok]
      have hge : i.val = edges.val.length := by
        have : ¬ i.val < edges.val.length := hlt
        omega
      rw [hfound, hge]
      exact exists_idx_iff_mem edges.val (fun x => mutationCanonicalEdge x = edge)
  · exact ⟨by simp, by simp⟩

/-- The edit certifies `e` against the published tree `t`: it adds `e`, or `e` is a tree edge that
the edit does not remove. -/
def TreeCert (t : spanning_tree.Tree) (rem add : Slice topology.Edge) (e : topology.Edge) : Prop :=
  scene.contains add e = ok true ∨
    (spanning_tree.Tree.has_edge t e = ok true ∧ scene.contains rem e = ok false)

/-- Every edge in the scratch list is certified (vacuous while no tree is published). -/
def CertList (tree : Option spanning_tree.Tree) (rem add : Slice topology.Edge)
    (req : alloc.vec.Vec topology.Edge) : Prop :=
  ∀ t, tree = some t → ∀ e ∈ req.val, TreeCert t rem add e

theorem route_admit_cert (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge) (e : topology.Edge) (req : alloc.vec.Vec topology.Edge)
    (hcert : ∀ t, tree = some t → TreeCert t rem add e) :
    OkPost (routeAdmit L e req) (fun p =>
      CertList tree rem add req → CertList tree rem add p.2) := by
  unfold routeAdmit
  refine okPost_bind (okPost_trivial _) ?_
  intro b _
  by_cases hb : b = true
  · simp only [hb, ↓reduceIte]
    exact okPost_ok (fun h => h)
  · simp only [hb]
    refine okPost_bind (okPost_trivial _) ?_
    intro s1 _
    by_cases hi : alloc.vec.Vec.len req = Slice.len s1
    · simp only [hi, ↓reduceIte]
      exact okPost_ok (fun h => h)
    · simp only [hi, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r1 hr1 _
      have hv := vec_push_ok _ _ _ hr1
      refine okPost_ok (fun h t ht x hx => ?_)
      rw [hv] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h t ht x hx
      · rw [List.mem_singleton.mp hx]; exact hcert t ht

/-- One edge check keeps the scratch list certified. -/
theorem check_route_edge_cert (L : scene.Layout)
    (edge : core.result.Result (Option topology.Edge) topology.Error)
    (phases next : Slice Std.I32) (pub : scene.RoutePublication)
    (req : alloc.vec.Vec topology.Edge) :
    OkPost (scene.check_route_edge L edge phases next pub req) (fun p =>
      CertList pub.current_tree pub.remove pub.add req →
        CertList pub.current_tree pub.remove pub.add p.2) := by
  unfold scene.check_route_edge
  cases edge with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok (fun h => h)
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    cases val with
    | none => exact okPost_ok (fun h => h)
    | some e =>
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r hdoor _
      cases r with
      | Err y =>
        simp only [Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        exact okPost_ok (fun h => h)
      | Ok d =>
        simp only [Std.bind_ok]
        cases hct : pub.current_tree with
        | none =>
          simp only
          exact okPost_mono (route_admit_cert L none pub.remove pub.add e req
            (fun t ht => by simp at ht)) (fun p hp h => by
              intro t ht; simp at ht)
        | some current =>
          simp only
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro b hbe _
          by_cases hb : b = true
          · simp only [hb]
            exact okPost_mono (route_admit_cert L (some current) pub.remove pub.add e req
              (fun t ht => by
                cases Option.some.inj ht
                exact Or.inl (by rw [hbe, hb]))) (fun p hp => hp)
          · simp only [hb, Bool.false_eq_true, ↓reduceIte]
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro b1 hb1e _
            by_cases hb1 : b1 = true
            · simp only [hb1]
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro b2 hb2e _
              by_cases hb2 : b2 = true
              · simp only [hb2]
                exact okPost_ok (fun h => h)
              · have hb2f : b2 = false := by simpa using hb2
                simp only [hb2]
                exact okPost_mono (route_admit_cert L (some current) pub.remove pub.add e req
                  (fun t ht => by
                    cases Option.some.inj ht
                    exact Or.inr ⟨by rw [hb1e, hb1], by rw [hb2e, hb2f]⟩)) (fun p hp => hp)
            · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
              exact okPost_ok (fun h => h)

theorem check_route_loop_body_cert (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize)
    (hreq : CertList pub.current_tree pub.remove pub.add req) :
    OkPost (scene.check_route_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (fun y => match y with
        | .cont s => CertList pub.current_tree pub.remove pub.add s.1
        | .done y => CertList pub.current_tree pub.remove pub.add y.1) := by
  unfold scene.check_route_loop.body
  by_cases hlt : i2 < alloc.vec.Vec.len route.cells
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro cell _
      refine okPost_bind (okPost_trivial _) ?_
      intro r _
      refine okPost_bind (okPost_trivial _) ?_
      intro e _
      refine okPost_bind (okPost_trivial _) ?_
      rintro ⟨interior1, r1⟩ _
      refine okPost_bind (m := scene.check_route_edge L r1 phases next pub req)
        (check_route_edge_cert L r1 phases next pub req) ?_
      rintro ⟨st1, req1⟩ hpost
      refine okPost_bind (okPost_trivial _) ?_
      intro i4 _
      exact okPost_ok (hpost hreq)
    · simp only [hb]
      exact okPost_ok hreq
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hreq

theorem check_route_loop_cert (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize)
    (hreq : CertList pub.current_tree pub.remove pub.add req) :
    OkPost (scene.check_route_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (fun y => CertList pub.current_tree pub.remove pub.add y.1) := by
  unfold scene.check_route_loop
  refine okPost_loop (fun s => CertList pub.current_tree pub.remove pub.add s.1)
    (fun y : (alloc.vec.Vec topology.Edge) × (core.result.Result Unit topology.Error) × Bool =>
      CertList pub.current_tree pub.remove pub.add y.1) _ ?_ (req, st, interior, prev, i2) hreq
  rintro ⟨req, st, interior, prev, i2⟩ h
  dsimp only
  refine okPost_mono (check_route_loop_body_cert L pub phases next route req st interior
    prev i2 h) ?_
  intro y hy
  cases y <;> exact hy

theorem check_route_cert (L : scene.Layout) (route : scene.Route) (circle : Std.Usize)
    (phases next : Slice Std.I32) (pub : scene.RoutePublication)
    (req : alloc.vec.Vec topology.Edge)
    (hreq : CertList pub.current_tree pub.remove pub.add req) :
    OkPost (scene.check_route L route circle phases next pub req)
      (fun p => CertList pub.current_tree pub.remove pub.add p.2) := by
  unfold scene.check_route
  by_cases h1 : (route.circle != circle) = true
  · simp only [h1, ↓reduceIte]
    exact okPost_ok hreq
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : alloc.vec.Vec.len route.cells < 7#usize
    · simp only [h2, ↓reduceIte]
      exact okPost_ok hreq
    · simp only [h2, ↓reduceIte]
      by_cases h3 : alloc.vec.Vec.len route.cells > alloc.vec.Vec.len L.cells
      · simp only [h3, ↓reduceIte]
        exact okPost_ok hreq
      · simp only [h3, ↓reduceIte]
        refine okPost_bind (check_route_loop_cert L pub phases next route req
          (core.result.Result.Ok ()) false 0#usize 0#usize hreq) ?_
        rintro ⟨req1, st1, interior⟩ h1
        refine okPost_bind (okPost_trivial _) ?_
        intro cf _
        cases cf with
        | Continue v =>
          simp only
          by_cases hi : interior = true
          · simp only [hi, ↓reduceIte]
            exact okPost_ok h1
          · simp only [hi]
            exact okPost_ok h1
        | Break v =>
          simp only
          refine okPost_bind (okPost_trivial _) ?_
          intro r _
          exact okPost_ok h1

theorem check_routes_loop_body_cert (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize) (hreq : CertList tree rem add req) :
    OkPost (scene.check_routes_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add tree req st r)
      (fun y => match y with
        | .cont s => CertList tree rem add s.1
        | .done y => CertList tree rem add y.2) := by
  unfold scene.check_routes_loop.body
  by_cases hlt : r < Slice.len routes
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro r1 _
      refine okPost_bind (m := scene.check_route L r1 r phases next ⟨tree, rem, add⟩ req)
        (check_route_cert L r1 r phases next ⟨tree, rem, add⟩ req hreq) ?_
      rintro ⟨st1, req1⟩ h1
      refine okPost_bind (okPost_trivial _) ?_
      intro r2 _
      exact okPost_ok h1
    · simp only [hb]
      exact okPost_ok hreq
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hreq

theorem check_routes_loop_cert (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize) (hreq : CertList tree rem add req) :
    OkPost (scene.check_routes_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add req tree st r)
      (fun y => CertList tree rem add y.2) := by
  unfold scene.check_routes_loop
  refine okPost_loop (fun s => CertList tree rem add s.1)
    (fun y : (core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge) =>
      CertList tree rem add y.2) _ ?_ (req, st, r) hreq
  rintro ⟨req, st, r⟩ h
  dsimp only
  refine okPost_mono (check_routes_loop_body_cert L tree rem add phases next routes req st r
    h) ?_
  intro y hy
  cases y <;> exact hy

/-- Every edge `check_routes` leaves in `required` is certified against the edit: added by it, or a
tree edge it does not remove (when a tree is published). -/
theorem scene_check_routes_cert (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (tree : Option spanning_tree.Tree) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) :
    OkPost (scene.check_routes L routes phases next tree edit req)
      (fun p => p.1 = core.result.Result.Ok () → CertList tree edit.remove edit.add p.2) := by
  unfold scene.check_routes
  by_cases hne : (Slice.len routes != alloc.vec.Vec.len L.circles) = true
  · simp only [hne, ↓reduceIte]
    exact okPost_ok (fun h => by simp at h)
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine okPost_bind (okPost_of_spec (vec_clear_spec alloc.alloc.Global req)) ?_
    intro req1 hreq1
    refine okPost_mono (check_routes_loop_cert L tree edit.remove edit.add phases next routes
      req1 (core.result.Result.Ok ()) 0#usize (fun t _ e he => by simp [hreq1] at he)) ?_
    intro y hy _; exact hy

theorem route_edge_list_le (cs : List Std.Usize) (e : topology.Edge) (h : e ∈ routeEdgeList cs) :
    e.u.val ≤ e.v.val := by
  induction cs with
  | nil => simp [routeEdgeList] at h
  | cons a rest ih =>
    cases rest with
    | nil => simp [routeEdgeList] at h
    | cons b rest' =>
      simp only [routeEdgeList, List.mem_cons] at h
      rcases h with rfl | h
      · unfold constructorCanonicalEdge
        split
        · assumption
        · rename_i hn; dsimp only; simp only [UScalar.le_equiv] at hn; omega
      · exact ih h

theorem all_edges_le (routes : List scene.Route) (e : topology.Edge) (h : e ∈ allEdges routes) :
    e.u.val ≤ e.v.val := by
  unfold allEdges at h
  obtain ⟨rt, _, hrt⟩ := List.mem_flatMap.mp h
  exact route_edge_list_le _ e hrt

theorem canonical_of_le (e : topology.Edge) (h : e.u.val ≤ e.v.val) :
    mutationCanonicalEdge e = e := by
  unfold mutationCanonicalEdge
  have : e.u ≤ e.v := by simpa [UScalar.le_equiv] using h
  simp [this]

theorem tree_cert_edited (t : spanning_tree.Tree) (rem add : Slice topology.Edge)
    (e : topology.Edge) (hle : e.u.val ≤ e.v.val) (h : TreeCert t rem add e) :
    MutationEditedEdge (parents t) rem add e.u.val e.v.val := by
  rcases h with h | ⟨h1, h2⟩
  · refine Or.inr ?_
    have hs := scene_contains_spec add e
    rw [h] at hs
    obtain ⟨x, hx, hxe⟩ := ((spec_ok _).mp hs).mp rfl
    refine ⟨x, hx, ?_⟩
    unfold mutationCanonicalEdge at hxe
    split at hxe
    · subst hxe; exact Or.inl ⟨rfl, rfl⟩
    · rw [← hxe]; exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨?_, ?_⟩
    · have hs := mutation_has_edge_total t e
      rw [h1] at hs
      exact ((spec_ok _).mp hs).mp rfl
    · have hs := scene_contains_spec rem e
      rw [h2] at hs
      have hno := (spec_ok _).mp hs
      rintro ⟨x, hx, hxe⟩
      have : ¬ ∃ x ∈ rem.val, mutationCanonicalEdge x = e := fun hex => by
        have := hno.mpr hex; simp at this
      apply this
      refine ⟨x, hx, ?_⟩
      unfold mutationCanonicalEdge
      obtain ⟨xu, xv⟩ := x
      obtain ⟨eu, ev⟩ := e
      simp only at hxe hle
      rcases hxe with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · have : xu ≤ xv := by simp [UScalar.le_equiv, h3, h4, hle]
        simp only [this, ite_true]
        congr 1 <;> exact UScalar.eq_of_val_eq (by simp_all)
      · by_cases hq : xu ≤ xv
        · simp only [hq, ite_true]
          have : xu.val ≤ xv.val := hq
          have h5 : eu.val = ev.val := by omega
          congr 1 <;> exact UScalar.eq_of_val_eq (by omega)
        · simp only [hq, ite_false]
          congr 1 <;> exact UScalar.eq_of_val_eq (by omega)

/-- `check_routes` with a published tree: on success every route edge (of the given routes) is
either added by the edit or a tree edge the edit does not remove. -/
theorem scene_check_routes_route_certificate (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (t : spanning_tree.Tree) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (hc : CarrierValid L.carrier)
    (hinv : RouteInv L.carrier req) :
    OkPost (scene.check_routes L routes phases next (some t) edit req) (fun p =>
      p.1 = core.result.Result.Ok () →
        ∀ e ∈ allEdges routes.val,
          MutationEditedEdge (parents t) edit.remove edit.add e.u.val e.v.val) := by
  intro v hv hst e he
  obtain ⟨_, hok, _⟩ := scene_check_routes_required_exact L routes phases next (some t)
    edit req hc hinv v hv
  have hcert := scene_check_routes_cert L routes phases next (some t) edit req v hv
  obtain ⟨st, req'⟩ := v
  have hmem : e ∈ req'.val := by
    rw [hok hst, foldEdges_mem]; exact Or.inr he
  exact tree_cert_edited t edit.remove edit.add e (all_edges_le _ e he)
    (hcert hst t rfl e hmem)

end Labyrinth
