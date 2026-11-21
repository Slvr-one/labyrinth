module
public import LabyrinthCore.SceneStd
public import LabyrinthCore.MutationValidate
public import LabyrinthCore.ConstructorSceneInitialize
import all Init.Internal.Order.Basic

/-! Route budget (S1). `scene::check_route_edge`, `check_route`, `check_routes` keep the scratch list
`required` duplicate-free and inside the carrier's edge list, so the `InsufficientWorkspace` branch
(`required.len == carrier.edges().len()`) is unreachable for a valid carrier. This is a logical
claim, not a capacity claim.

The calls reach `Layout::doorway`, whose geometry is not shown to be total here, so the statements
are partial correctness: they hold of every result the call returns (`OkPost`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result Lean.Order labyrinth_core

namespace Labyrinth

/-- Partial correctness: every returned value satisfies `P` (failure and divergence are allowed). -/
def OkPost {α : Type _} (x : Result α) (P : α → Prop) : Prop := ∀ v, x = ok v → P v

unseal Aeneas.Std.Result in
theorem okPost_admissible {α : Type _} (P : α → Prop) :
    admissible (fun m : Result α => OkPost m P) := by
  intro c hc hAll v hv
  have h := Aeneas.Data.Coinductive.ITree.csup_ret_mem hc (value := v) hv
  exact hAll _ h v rfl

theorem okPost_loop_adm {α β : Type _} (inv : α → Prop) (post : β → Prop) :
    admissible (fun f : α → Result β => ∀ x, inv x → OkPost (f x) post) :=
  admissible_pi_apply (fun x (m : Result β) => inv x → OkPost m post)
    (fun x => by
      intro c hc hAll hx
      exact okPost_admissible post c hc (fun m hm => hAll m hm hx))

theorem okPost_bind {α β : Type _} {m : Result α} {k : α → Result β} {P : α → Prop}
    {Q : β → Prop} (hm : OkPost m P) (hk : ∀ a, P a → OkPost (k a) Q) :
    OkPost (Std.bind m k) Q := by
  intro v hv
  cases m using Result.cases with
  | ret a =>
    rw [Std.bind_ok] at hv
    exact hk a (hm a rfl) v hv
  | vis e k' =>
    rw [Std.bind_vis] at hv
    exact absurd hv vis_not_ok
  | div =>
    rw [Std.bind_div] at hv
    exact absurd hv div_not_ok

theorem okPost_bind_eq {α β : Type _} {m : Result α} {k : α → Result β} {P : α → Prop}
    {Q : β → Prop} (hm : OkPost m P) (hk : ∀ a, m = ok a → P a → OkPost (k a) Q) :
    OkPost (Std.bind m k) Q := by
  intro v hv
  cases m using Result.cases with
  | ret a =>
    rw [Std.bind_ok] at hv
    exact hk a rfl (hm a rfl) v hv
  | vis e k' =>
    rw [Std.bind_vis] at hv
    exact absurd hv vis_not_ok
  | div =>
    rw [Std.bind_div] at hv
    exact absurd hv div_not_ok

theorem okPost_ok {α : Type _} {P : α → Prop} {a : α} (h : P a) : OkPost (ok a) P := by
  intro v hv; simp at hv; subst hv; exact h

theorem okPost_mono {α : Type _} {m : Result α} {P Q : α → Prop} (h : OkPost m P)
    (hPQ : ∀ a, P a → Q a) : OkPost m Q := fun v hv => hPQ v (h v hv)

theorem okPost_of_spec {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    OkPost m P := by
  intro v hv; rw [hv] at h; exact (spec_ok (p := P) v).mp h

theorem okPost_trivial {α : Type _} (m : Result α) : OkPost m (fun _ => True) :=
  fun _ _ => trivial

theorem okPost_loop {α β : Type _} (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ x, inv x → OkPost (body x) (fun r => match r with
      | .cont x' => inv x' | .done y => post y)) :
    ∀ x, inv x → OkPost (loop body x) post := by
  refine loop.fixpoint_induct body (fun f => ∀ x, inv x → OkPost (f x) post)
    (okPost_loop_adm inv post) ?_
  intro f ih x hx
  refine okPost_bind (m := body x) (hBody x hx) ?_
  intro r hr
  cases r with
  | cont x' => exact ih x' hr
  | done y => exact okPost_ok hr


/-! ### The admission block -/

/-- The block `check_route_edge` runs once an edge has passed the doorway test (the source repeats
it in each arm). -/
def routeAdmit (layout : scene.Layout) (edge : topology.Edge)
    (required : alloc.vec.Vec topology.Edge) :
    Result ((core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge)) := do
  let s := alloc.vec.Vec.deref required
  let b ← core.slice.Slice.contains topology.Edge.Insts.CoreCmpPartialEqEdge s edge
  if b
  then ok (core.result.Result.Ok (), required)
  else
    let i := alloc.vec.Vec.len required
    let s1 ← topology.Carrier.impl.edges layout.carrier
    let i1 := Slice.len s1
    if i = i1
    then ok (core.result.Result.Err topology.Error.InsufficientWorkspace, required)
    else
      let required1 ← alloc.vec.Vec.push required edge
      ok (core.result.Result.Ok (), required1)

/-- The scratch list stays duplicate-free and inside the carrier's edges. -/
def RouteInv (c : topology.Carrier) (required : alloc.vec.Vec topology.Edge) : Prop :=
  required.val.Nodup ∧ ∀ e ∈ required.val, e ∈ c.edges.val

/-- A duplicate-free list inside the carrier's edges that misses an edge of the carrier is
strictly shorter than the carrier's edge list. -/
theorem route_required_length_lt (c : topology.Carrier) (required : alloc.vec.Vec topology.Edge)
    (e : topology.Edge) (hinv : RouteInv c required) (hin : e ∈ c.edges.val)
    (hnot : e ∉ required.val) : required.val.length < c.edges.val.length := by
  have hnd : (e :: required.val).Nodup := List.nodup_cons.mpr ⟨hnot, hinv.1⟩
  have hsub : (e :: required.val) ⊆ c.edges.val := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hin
    · exact hinv.2 x hx
  have := (hnd.subperm hsub).length_le
  simpa using this

/-- Admission appends the edge when absent, never reports `InsufficientWorkspace`, and keeps the
scratch invariant. -/
theorem route_admit_spec (layout : scene.Layout) (edge : topology.Edge)
    (required : alloc.vec.Vec topology.Edge) (hinv : RouteInv layout.carrier required)
    (hin : edge ∈ layout.carrier.edges.val) :
    routeAdmit layout edge required ⦃ p =>
      p.1 = core.result.Result.Ok () ∧
      (edge ∈ required.val → p.2.val = required.val) ∧
      (edge ∉ required.val → p.2.val = required.val ++ [edge]) ⦄ := by
  unfold routeAdmit
  apply spec_bind (slice_contains_edge_spec (alloc.vec.Vec.deref required) edge)
  intro b hb
  have hmem : b = true ↔ edge ∈ required.val := by simpa [alloc.vec.Vec.deref] using hb
  by_cases hbt : b = true
  · have h := hmem.mp hbt
    simp [hbt, spec_ok, h]
  · have hbf : b = false := by simpa using hbt
    have hnot : edge ∉ required.val := fun h => hbt (hmem.mpr h)
    have hlt := route_required_length_lt layout.carrier required edge hinv hin hnot
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    have hedges : topology.Carrier.impl.edges layout.carrier =
        ok (alloc.vec.Vec.deref layout.carrier.edges) := rfl
    rw [hedges, bind_ok]
    have hne : ¬ (alloc.vec.Vec.len required =
        Slice.len (alloc.vec.Vec.deref layout.carrier.edges)) := by
      intro h
      have := congrArg (·.val) h
      simp [alloc.vec.Vec.deref] at this
      omega
    simp only [hne, ↓reduceIte]
    have hcap : required.val.length < Usize.max := by
      have := layout.carrier.edges.property
      scalar_tac
    apply spec_bind (alloc.vec.Vec.push_spec required edge hcap)
    intro r hr
    simp [spec_ok, hr]
    exact fun h => absurd h hnot


/-! ### The doorway guard -/

/-- A doorway that is admitted (`Ok`) first passed `carrier.contains_edge`. -/
theorem layout_doorway_ok_carrier_edge (layout : scene.Layout) (edge : topology.Edge)
    (phases next : Slice Std.I32) (hc : CarrierValid layout.carrier) :
    OkPost (scene.Layout.doorway layout edge phases next) (fun r =>
      r.ok? = true → carrierEdge layout.carrier edge.u.val edge.v.val) := by
  unfold scene.Layout.doorway
  by_cases hu : edge.u ≥ alloc.vec.Vec.len layout.cells
  · simp only [hu, ↓reduceIte]
    exact okPost_ok (by simp)
  · by_cases hv : edge.v ≥ alloc.vec.Vec.len layout.cells
    · simp only [hu, hv, ↓reduceIte]
      exact okPost_ok (by simp)
    · simp only [hu, hv, ↓reduceIte]
      refine okPost_bind (okPost_of_spec (mutation_carrier_contains_total layout.carrier edge hc)) ?_
      intro b hb
      by_cases hbt : b = true
      · intro v _ _
        exact hb.mp hbt
      · have hbf : b = false := by simpa using hbt
        simp only [hbf, Bool.false_eq_true, ↓reduceIte]
        exact okPost_ok (by simp)

/-- A carrier edge written with `u ≤ v` is one of the carrier's listed edges. -/
theorem carrier_edge_mem_edges (c : topology.Carrier) (hc : CarrierValid c) (edge : topology.Edge)
    (horder : edge.u.val ≤ edge.v.val) (h : carrierEdge c edge.u.val edge.v.val) :
    edge ∈ c.edges.val := by
  have hu := h.1
  have hne : edge.u.val ≠ edge.v.val := by
    intro heq
    have hself := (hc.2.2.2.2.1 edge.u.val hu).2.1
    rw [heq] at hself hu
    exact hself (heq ▸ h.2)
  have hpair : (edge.u.val, edge.v.val) ∈ edgePairs c :=
    (hc.2.2.2.2.2.2.2 _ _).mpr ⟨by omega, h⟩
  obtain ⟨e', he', hee⟩ := List.mem_map.mp hpair
  have hu' : e'.u.val = edge.u.val := congrArg Prod.fst hee
  have hv' : e'.v.val = edge.v.val := congrArg Prod.snd hee
  have : e' = edge := by
    cases e'; cases edge
    simp only [topology.Edge.mk.injEq]
    exact ⟨UScalar.eq_of_val_eq hu', UScalar.eq_of_val_eq hv'⟩
  exact this ▸ he'


/-! ### `check_route_edge` -/

/-- Where an error of one edge check comes from: it is the input error, the doorway's error, or the
`InvalidTransition` of the tree-publication test. -/
def RouteEdgeError (layout : scene.Layout) (publication : scene.RoutePublication)
    (edge : core.result.Result (Option topology.Edge) topology.Error)
    (phases next : Slice Std.I32) (x : topology.Error) : Prop :=
  edge = core.result.Result.Err x ∨
  ∃ e, edge = core.result.Result.Ok (some e) ∧
    (scene.Layout.doorway layout e phases next = ok (core.result.Result.Err x) ∨
      (x = topology.Error.InvalidTransition ∧
        ∃ t, publication.current_tree = some t ∧
          scene.contains publication.add e = ok false ∧
          (spanning_tree.Tree.has_edge t e = ok false ∨
            scene.contains publication.remove e = ok true)))

/-- What one edge check guarantees about the scratch list. The only `InsufficientWorkspace` it can
return is one handed in (`edge = Err _`) or produced by `Layout::doorway` (its hold table); the
`required.len == carrier.edges().len` branch never fires. Every error leaves the list unchanged,
the invariant is kept, and success appends the edge when it was absent. -/
def RouteEdgePost (layout : scene.Layout) (publication : scene.RoutePublication)
    (edge : core.result.Result (Option topology.Edge) topology.Error)
    (phases next : Slice Std.I32)
    (required : alloc.vec.Vec topology.Edge)
    (p : (core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge)) : Prop :=
  (p.1 = core.result.Result.Err topology.Error.InsufficientWorkspace →
    edge = core.result.Result.Err topology.Error.InsufficientWorkspace ∨
    ∃ e, edge = core.result.Result.Ok (some e) ∧
      scene.Layout.doorway layout e phases next =
        ok (core.result.Result.Err topology.Error.InsufficientWorkspace)) ∧
  RouteInv layout.carrier p.2 ∧
  (∀ x, p.1 = core.result.Result.Err x → p.2 = required ∧
    RouteEdgeError layout publication edge phases next x) ∧
  (p.1 = core.result.Result.Ok () → edge = core.result.Result.Ok none → p.2 = required) ∧
  (p.1 = core.result.Result.Ok () → ∀ e, edge = core.result.Result.Ok (some e) →
    (e ∈ required.val → p.2.val = required.val) ∧
    (e ∉ required.val → p.2.val = required.val ++ [e])) ∧
  (∀ x, edge = core.result.Result.Err x → p.1 = core.result.Result.Err x)

theorem route_admit_post (layout : scene.Layout) (publication : scene.RoutePublication)
    (edge : core.result.Result (Option topology.Edge) topology.Error) (e : topology.Edge) (he : edge = core.result.Result.Ok (some e))
    (phases next : Slice Std.I32)
    (required : alloc.vec.Vec topology.Edge) (hinv : RouteInv layout.carrier required)
    (hin : e ∈ layout.carrier.edges.val) :
    OkPost (routeAdmit layout e required)
      (RouteEdgePost layout publication edge phases next required) := by
  apply okPost_of_spec
  apply spec_mono (route_admit_spec layout e required hinv hin)
  rintro ⟨st, req⟩ ⟨hst, hadd⟩
  simp only at hst hadd
  subst hst
  have hreq : RouteInv layout.carrier req := by
    by_cases hm : e ∈ required.val
    · have := hadd.1 hm
      exact ⟨by rw [this]; exact hinv.1, by rw [this]; exact hinv.2⟩
    · have := hadd.2 hm
      refine ⟨by
        rw [this]
        exact List.nodup_append.mpr ⟨hinv.1, List.nodup_singleton e,
          fun a ha b hb hab => hm (by rw [List.mem_singleton.mp hb] at hab; exact hab ▸ ha)⟩, ?_⟩
      intro x hx
      rw [this] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hinv.2 x hx
      · rw [List.mem_singleton.mp hx]; exact hin
  refine ⟨by simp, hreq, by simp, ?_, ?_, ?_⟩
  · intro _ h; rw [he] at h; simp at h
  · intro _ e' he'
    rw [he] at he'
    simp only [core.result.Result.Ok.injEq, Option.some.injEq] at he'
    subst he'
    exact hadd
  · intro x h; rw [he] at h; simp at h


theorem route_edge_post_err (layout : scene.Layout) (publication : scene.RoutePublication)
    (edge : core.result.Result (Option topology.Edge) topology.Error) (phases next : Slice Std.I32)
    (required : alloc.vec.Vec topology.Edge) (hinv : RouteInv layout.carrier required)
    (x : topology.Error) (herr : RouteEdgeError layout publication edge phases next x)
    (hedge : ∀ y, edge = core.result.Result.Err y → y = x) :
    RouteEdgePost layout publication edge phases next required
      (core.result.Result.Err x, required) := by
  refine ⟨?_, hinv, fun y hy => ?_, by simp, by simp, ?_⟩
  · intro h
    simp only [core.result.Result.Err.injEq] at h
    subst h
    rcases herr with h | ⟨e, he, h | ⟨hx, _⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he, h⟩
    · exact absurd hx (by simp)
  · simp only [core.result.Result.Err.injEq] at hy
    subst hy
    exact ⟨rfl, herr⟩
  · intro y hy
    rw [hedge y hy]

theorem scene_check_route_edge_budget (layout : scene.Layout)
    (edge : core.result.Result (Option topology.Edge) topology.Error)
    (phases next : Slice Std.I32) (publication : scene.RoutePublication)
    (required : alloc.vec.Vec topology.Edge) (hc : CarrierValid layout.carrier)
    (hinv : RouteInv layout.carrier required)
    (hnorm : ∀ e, edge = core.result.Result.Ok (some e) → e.u.val ≤ e.v.val) :
    OkPost (scene.check_route_edge layout edge phases next publication required)
      (RouteEdgePost layout publication edge phases next required) := by
  unfold scene.check_route_edge
  cases edge with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok (route_edge_post_err layout publication _ phases next required hinv x
      (Or.inl rfl) (by simp))
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    cases val with
    | none => exact okPost_ok ⟨by simp, hinv, by simp, by simp, by simp, by simp⟩
    | some e =>
      have he := hnorm e rfl
      refine okPost_bind_eq (layout_doorway_ok_carrier_edge layout e phases next hc) ?_
      intro r hdoor hr
      cases r with
      | Err y =>
        simp only [Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        exact okPost_ok (route_edge_post_err layout publication _ phases next required hinv y
          (Or.inr ⟨e, rfl, Or.inl hdoor⟩) (by simp))
      | Ok d =>
        have hin : e ∈ layout.carrier.edges.val :=
          carrier_edge_mem_edges _ hc e he (hr rfl)
        simp only [Std.bind_ok]
        have hadm := route_admit_post layout publication _ e rfl phases next required hinv hin
        have hinvalid : ∀ t, publication.current_tree = some t →
            scene.contains publication.add e = ok false →
            (spanning_tree.Tree.has_edge t e = ok false ∨
              scene.contains publication.remove e = ok true) →
            OkPost (ok (core.result.Result.Err topology.Error.InvalidTransition,
              required) : Result _) (RouteEdgePost layout publication
                (core.result.Result.Ok (some e)) phases next required) := by
          intro t ht h1 h2
          exact okPost_ok (route_edge_post_err _ _ _ _ _ _ hinv _
            (Or.inr ⟨e, rfl, Or.inr ⟨rfl, t, ht, h1, h2⟩⟩) (by simp))
        cases hct : publication.current_tree with
        | none =>
          simp only
          exact hadm
        | some current =>
          simp only
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro b hbe _
          by_cases hb : b = true
          · simp only [hb]
            exact hadm
          · have hbf : b = false := by simpa using hb
            subst hbf
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro b1 hb1e _
            by_cases hb1 : b1 = true
            · simp only [hb1]
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro b2 hb2e _
              by_cases hb2 : b2 = true
              · simp only [hb2]
                exact hinvalid current hct hbe (Or.inr (by rw [hb2e, hb2]))
              · simp only [hb2]
                exact hadm
            · have hb1f : b1 = false := by simpa using hb1
              subst hb1f
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hinvalid current hct hbe (Or.inl hb1e)


/-! ### The route edge list and its first-occurrence fold -/

/-- The canonical edges along a route: consecutive cells joined by `Edge::new`. -/
def routeEdgeList : List Std.Usize → List topology.Edge
  | a :: b :: rest => constructorCanonicalEdge ⟨a, b⟩ :: routeEdgeList (b :: rest)
  | _ => []

/-- Append `e` unless the list already holds it. -/
noncomputable def addEdge (acc : List topology.Edge) (e : topology.Edge) : List topology.Edge :=
  open Classical in if e ∈ acc then acc else acc ++ [e]

/-- Fold edges into a list, keeping only the first occurrence of each: exactly what repeated
`check_route_edge` calls do to `required`. -/
noncomputable def foldEdges (acc es : List topology.Edge) : List topology.Edge :=
  es.foldl addEdge acc

@[simp] theorem foldEdges_nil (acc : List topology.Edge) : foldEdges acc [] = acc := rfl

theorem foldEdges_append (acc es fs : List topology.Edge) :
    foldEdges acc (es ++ fs) = foldEdges (foldEdges acc es) fs := by
  simp [foldEdges, List.foldl_append]

theorem foldEdges_nodup (acc es : List topology.Edge) (h : acc.Nodup) :
    (foldEdges acc es).Nodup := by
  induction es generalizing acc with
  | nil => exact h
  | cons e es ih =>
    simp only [foldEdges, List.foldl_cons] at ih ⊢
    apply ih
    unfold addEdge
    classical
    split
    · exact h
    · exact List.nodup_append.mpr ⟨h, List.nodup_singleton e,
        fun a ha b hb hab => by
          rename_i hn
          exact hn (by rw [List.mem_singleton.mp hb] at hab; exact hab ▸ ha)⟩

theorem foldEdges_mem (acc es : List topology.Edge) (x : topology.Edge) :
    x ∈ foldEdges acc es ↔ x ∈ acc ∨ x ∈ es := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [foldEdges, List.foldl_cons] at ih ⊢
    rw [ih]
    unfold addEdge
    classical
    split
    · rename_i hm
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hm
          · exact Or.inr h
    · simp [or_assoc, or_comm, or_left_comm]

theorem routeEdgeList_take_succ (cs : List Std.Usize) (i : Nat) (hi : 1 ≤ i) (hlt : i < cs.length) :
    routeEdgeList (cs.take (i + 1)) =
      routeEdgeList (cs.take i) ++ [constructorCanonicalEdge ⟨cs[i - 1], cs[i]⟩] := by
  induction cs generalizing i with
  | nil => simp at hlt
  | cons a cs ih =>
    cases cs with
    | nil => simp at hlt; omega
    | cons b cs =>
      cases i with
      | zero => omega
      | succ i =>
        cases i with
        | zero => simp [routeEdgeList]
        | succ i =>
          have := ih (i + 1) (by omega) (by simpa using hlt)
          simp only [List.take_succ_cons, routeEdgeList] at this ⊢
          rw [this]
          simp


/-! ### One route -/

/-- What `route_cell_status` hands to the edge check: the cell's own error, else no edge for the
first cell and the connecting edge for every later one. -/
def cellEdge (r : core.result.Result Bool topology.Error) (first : Bool) (e : topology.Edge) :
    core.result.Result (Option topology.Edge) topology.Error :=
  match r with
  | .Ok _ => .Ok (if first then none else some e)
  | .Err x => .Err x

/-- The edge joining cell `k - 1` to cell `k` of a route. -/
def stepEdge (cs : List Std.Usize) (k : Nat) : topology.Edge :=
  constructorCanonicalEdge ⟨cs.getD (k - 1) 0#usize, cs.getD k 0#usize⟩

/-- Cell `k` of the route fails with `x`: the cell check errs, or the edge check it leads to does. -/
def RouteStepFail (layout : scene.Layout) (publication : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route) (k : Nat) (x : topology.Error) : Prop :=
  ∃ ku : Std.Usize, ku.val = k ∧ ∃ r, scene.check_route_cell layout route ku = ok r ∧
    RouteEdgeError layout publication
      (cellEdge r (decide (k = 0)) (stepEdge route.cells.val k)) phases next x

/-- Loop state invariant of `check_route`: the scratch list is the first-occurrence fold of the
edges of the cells passed so far (`R0` is the list at route entry), or a recorded failure. -/
def RouteLoopInv (layout : scene.Layout) (publication : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route) (R0 : List topology.Edge)
    (s : (alloc.vec.Vec topology.Edge) × (core.result.Result Unit topology.Error) × Bool ×
      Std.Usize × Std.Usize) : Prop :=
  RouteInv layout.carrier s.1 ∧ s.2.2.2.2.val ≤ route.cells.val.length ∧
  (1 ≤ s.2.2.2.2.val → route.cells.val[s.2.2.2.2.val - 1]? = some s.2.2.2.1) ∧
  (s.2.1 = core.result.Result.Ok () →
    s.1.val = foldEdges R0 (routeEdgeList (route.cells.val.take s.2.2.2.2.val))) ∧
  (∀ x, s.2.1 = core.result.Result.Err x → ∃ k, k < route.cells.val.length ∧
    s.1.val = foldEdges R0 (routeEdgeList (route.cells.val.take k)) ∧
    RouteStepFail layout publication phases next route k x)

/-- The loop's exit condition. -/
def RouteLoopPost (layout : scene.Layout) (publication : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route) (R0 : List topology.Edge)
    (s : (alloc.vec.Vec topology.Edge) × (core.result.Result Unit topology.Error) × Bool) :
    Prop :=
  RouteInv layout.carrier s.1 ∧
  (s.2.1 = core.result.Result.Ok () → s.1.val = foldEdges R0 (routeEdgeList route.cells.val)) ∧
  (∀ x, s.2.1 = core.result.Result.Err x → ∃ k, k < route.cells.val.length ∧
    s.1.val = foldEdges R0 (routeEdgeList (route.cells.val.take k)) ∧
    RouteStepFail layout publication phases next route k x)

theorem route_cell_status_eq (interior : Bool) (r : core.result.Result Bool topology.Error)
    (first : Bool) (e : topology.Edge) :
    ∃ i', scene.route_cell_status interior r first e = ok (i', cellEdge r first e) := by
  cases r with
  | Ok b =>
    cases first <;> cases interior <;>
      simp [scene.route_cell_status, cellEdge]
  | Err x => simp [scene.route_cell_status, cellEdge]

theorem route_loop_body_post (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route) (R0 : List topology.Edge)
    (hc : CarrierValid L.carrier)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize)
    (hinv : RouteLoopInv L pub phases next route R0 (req, st, interior, prev, i2)) :
    OkPost (scene.check_route_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (fun r => match r with
        | .cont s' => RouteLoopInv L pub phases next route R0 s'
        | .done y => RouteLoopPost L pub phases next route R0 y) := by
  obtain ⟨hreq, hi2, hprev, hok, herr⟩ := hinv
  simp only at hreq hi2 hprev hok herr
  unfold scene.check_route_loop.body
  by_cases hlt : i2 < alloc.vec.Vec.len route.cells
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec st)) ?_
    intro b _ hb
    cases st with
    | Err x =>
      have hbf : b = false := by simpa using hb
      subst hbf
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok ⟨hreq, fun h => by simp at h, herr⟩
    | Ok u =>
      have hbt : b = true := by simpa using hb
      subst hbt
      simp only [↓reduceIte]
      have hi2lt : i2.val < route.cells.val.length := by simpa using hlt
      rw [alloc.vec.Vec.index_slice_index]
      refine okPost_bind (okPost_of_spec
        (alloc.vec.Vec.index_usize_spec route.cells i2 hi2lt)) ?_
      intro cell hcell
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r hrE _
      refine okPost_bind (okPost_of_spec (constructor_edge_new_spec ⟨prev, cell⟩)) ?_
      intro e he
      obtain ⟨i', hstat⟩ := route_cell_status_eq interior r (decide (i2 = 0#usize)) e
      rw [hstat]
      simp only [Std.bind_ok]
      have hnorm : ∀ e', cellEdge r (decide (i2 = 0#usize)) e = core.result.Result.Ok (some e') →
          e'.u.val ≤ e'.v.val := by
        intro e' h
        cases r with
        | Err x => simp [cellEdge] at h
        | Ok b =>
          simp only [cellEdge, core.result.Result.Ok.injEq] at h
          by_cases hf : decide (i2 = 0#usize) = true
          · simp [hf] at h
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
            subst h
            rw [he]
            unfold constructorCanonicalEdge
            split
            · rename_i h; simp only at h ⊢; scalar_tac
            · rename_i h; simp only at h ⊢; scalar_tac
      refine okPost_bind_eq (m := scene.check_route_edge L (cellEdge r (decide (i2 = 0#usize)) e)
        phases next pub req)
        (scene_check_route_edge_budget L _ phases next pub req hc hreq hnorm) ?_
      rintro ⟨st1, req1⟩ hcall hpost
      obtain ⟨_, hreq1, herr1, hnone1, hsome1, hinput1⟩ := hpost
      simp only at hreq1 herr1 hnone1 hsome1 hinput1
      have hadd : i2.val + 1 ≤ Usize.max := by
        have := route.cells.property
        scalar_tac
      refine okPost_bind (okPost_of_spec (Usize.add_spec (x := i2) (y := 1#usize) (by
        simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) ?_
      intro i4 hi4
      have hi4v : i4.val = i2.val + 1 := by simpa using hi4
      refine okPost_ok ?_
      have hcellv : route.cells.val[i2.val]? = some cell := by
        rw [List.getElem?_eq_getElem hi2lt, hcell]
      -- the connecting edge is the route's step edge
      have hedge : 1 ≤ i2.val → e = stepEdge route.cells.val i2.val := by
        intro h1
        have hp := hprev h1
        have hp' : route.cells.val.getD (i2.val - 1) 0#usize = prev := by
          simp [List.getD_eq_getElem?_getD, hp]
        have hc' : route.cells.val.getD i2.val 0#usize = cell := by
          simp [List.getD_eq_getElem?_getD, hcellv]
        rw [he]; unfold stepEdge; rw [hp', hc']
      have hfirst : cellEdge r (decide (i2 = 0#usize)) e =
          cellEdge r (decide (i2.val = 0)) (stepEdge route.cells.val i2.val) := by
        cases r with
        | Err x => rfl
        | Ok b =>
          by_cases h0 : i2.val = 0
          · have : i2 = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
            simp [cellEdge, this]
          · have h0' : ¬ i2 = 0#usize := fun h => h0 (by simp [h])
            simp [cellEdge, h0, h0', hedge (by omega)]
      refine ⟨hreq1, ?_, ?_, ?_, ?_⟩
      · show i4.val ≤ _
        omega
      · intro _
        show route.cells.val[i4.val - 1]? = some cell
        have : i4.val - 1 = i2.val := by omega
        rw [this]; exact hcellv
      · intro hst1'
        have hst1 : st1 = core.result.Result.Ok () := hst1'
        show req1.val = foldEdges R0 (routeEdgeList (route.cells.val.take i4.val))
        rw [hi4v]
        have hreqv : req.val = foldEdges R0 (routeEdgeList (route.cells.val.take i2.val)) :=
          hok rfl
        cases r with
        | Err x =>
          have := hinput1 x rfl
          rw [hst1] at this
          simp at this
        | Ok b =>
          by_cases h0 : i2.val = 0
          · have hi0 : i2 = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
            have hnone : cellEdge (core.result.Result.Ok b) (decide (i2 = 0#usize)) e =
                core.result.Result.Ok none := by simp [cellEdge, hi0]
            rw [hnone1 hst1 hnone, hreqv, h0]
            generalize route.cells.val = cs
            rcases cs with _ | ⟨a, t⟩ <;> simp [routeEdgeList]
          · have h1 : 1 ≤ i2.val := by omega
            have hi0 : ¬ i2 = 0#usize := fun h => h0 (by simp [h])
            have hsome : cellEdge (core.result.Result.Ok b) (decide (i2 = 0#usize)) e =
                core.result.Result.Ok (some e) := by simp [cellEdge, hi0]
            obtain ⟨hin, hnotin⟩ := hsome1 hst1 e hsome
            have hp := hprev h1
            have hprevv : prev = route.cells.val[i2.val - 1] := by
              rw [List.getElem?_eq_getElem (by omega)] at hp
              exact (Option.some.inj hp).symm
            have hcell' : cell = route.cells.val[i2.val] := hcell
            rw [routeEdgeList_take_succ _ _ h1 hi2lt, foldEdges_append, ← hreqv]
            have he' : e = constructorCanonicalEdge ⟨route.cells.val[i2.val - 1],
                route.cells.val[i2.val]⟩ := by rw [he, hprevv, hcell']
            rw [← he']
            show req1.val = addEdge req.val e
            unfold addEdge
            split
            · rename_i hm; exact hin hm
            · rename_i hm; exact hnotin hm
      · intro x hx
        obtain ⟨hreqx, herrx⟩ := herr1 x hx
        refine ⟨i2.val, hi2lt, ?_, i2, rfl, r, hrE, ?_⟩
        · rw [hreqx]; exact hok rfl
        · rw [← hfirst]; exact herrx
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok ⟨hreq, fun h => ?_, herr⟩
    have hn : ¬ i2.val < route.cells.val.length := by simpa using hlt
    have : i2.val = route.cells.val.length := by omega
    rw [hok h, this, List.take_length]

theorem route_loop_post (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route) (R0 : List topology.Edge)
    (hc : CarrierValid L.carrier)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize)
    (hinv : RouteLoopInv L pub phases next route R0 (req, st, interior, prev, i2)) :
    OkPost (scene.check_route_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (RouteLoopPost L pub phases next route R0) := by
  unfold scene.check_route_loop
  exact okPost_loop (RouteLoopInv L pub phases next route R0) (RouteLoopPost L pub phases next route R0)
    _ (by
      rintro ⟨req, st, interior, prev, i2⟩ h
      dsimp only
      refine okPost_mono (route_loop_body_post L pub phases next route R0 hc req st interior
        prev i2 h) ?_
      intro r hr
      cases r <;> exact hr)
    (req, st, interior, prev, i2) hinv

/-- How one route's check fails, with `R0` the list at entry and `final` the list at exit: a guard
(circle, length), the closing interior test, or the first failing cell/edge `k`, in which case the
list holds exactly the edges of the cells before `k`. -/
def RouteErr (L : scene.Layout) (pub : scene.RoutePublication) (phases next : Slice Std.I32)
    (circle : Std.Usize) (route : scene.Route) (R0 final : alloc.vec.Vec topology.Edge)
    (x : topology.Error) : Prop :=
  (x = topology.Error.InvalidGeometry ∧ final = R0 ∧
    (route.circle ≠ circle ∨ route.cells.val.length < 7 ∨
      L.cells.val.length < route.cells.val.length)) ∨
  (x = topology.Error.InvalidGeometry ∧
    final.val = foldEdges R0.val (routeEdgeList route.cells.val)) ∨
  (∃ k, k < route.cells.val.length ∧
    final.val = foldEdges R0.val (routeEdgeList (route.cells.val.take k)) ∧
    RouteStepFail L pub phases next route k x)

/-- One route's effect on the scratch list: success folds in the route's edges. -/
def CheckRoutePost (L : scene.Layout) (pub : scene.RoutePublication) (phases next : Slice Std.I32)
    (circle : Std.Usize) (route : scene.Route) (R0 : alloc.vec.Vec topology.Edge)
    (p : (core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge)) : Prop :=
  RouteInv L.carrier p.2 ∧
  (p.1 = core.result.Result.Ok () →
    p.2.val = foldEdges R0.val (routeEdgeList route.cells.val)) ∧
  (∀ x, p.1 = core.result.Result.Err x → RouteErr L pub phases next circle route R0 p.2 x)

theorem scene_check_route_budget (L : scene.Layout) (route : scene.Route) (circle : Std.Usize)
    (phases next : Slice Std.I32) (pub : scene.RoutePublication)
    (req : alloc.vec.Vec topology.Edge) (hc : CarrierValid L.carrier)
    (hinv : RouteInv L.carrier req) :
    OkPost (scene.check_route L route circle phases next pub req)
      (CheckRoutePost L pub phases next circle route req) := by
  unfold scene.check_route
  by_cases hcirc : (route.circle != circle) = true
  · simp only [hcirc, ↓reduceIte]
    refine okPost_ok ⟨hinv, by simp, fun x hx => Or.inl ⟨?_, rfl, Or.inl ?_⟩⟩
    · simpa using hx.symm
    · simpa using hcirc
  · simp only [hcirc, Bool.false_eq_true, ↓reduceIte]
    by_cases h7 : alloc.vec.Vec.len route.cells < 7#usize
    · simp only [h7, ↓reduceIte]
      refine okPost_ok ⟨hinv, by simp, fun x hx => Or.inl ⟨?_, rfl, Or.inr (Or.inl ?_)⟩⟩
      · simpa using hx.symm
      · simpa using h7
    · simp only [h7, ↓reduceIte]
      by_cases hgt : alloc.vec.Vec.len route.cells > alloc.vec.Vec.len L.cells
      · simp only [hgt, ↓reduceIte]
        refine okPost_ok ⟨hinv, by simp, fun x hx => Or.inl ⟨?_, rfl, Or.inr (Or.inr ?_)⟩⟩
        · simpa using hx.symm
        · simpa using hgt
      · simp only [hgt, ↓reduceIte]
        have hinv0 : RouteLoopInv L pub phases next route req.val
            (req, core.result.Result.Ok (), false, 0#usize, 0#usize) := by
          refine ⟨hinv, by simp, by simp, by simp [routeEdgeList], by simp⟩
        refine okPost_bind (route_loop_post L pub phases next route req.val hc req
          (core.result.Result.Ok ()) false 0#usize 0#usize hinv0) ?_
        rintro ⟨req1, st1, interior⟩ ⟨hreq1, hok1, herr1⟩
        simp only at hreq1 hok1 herr1
        cases st1 with
        | Ok u =>
          refine okPost_bind (okPost_of_spec
            (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u)) ?_
          intro cf hcf
          subst hcf
          by_cases hint : interior = true
          · simp only [hint, ↓reduceIte]
            exact okPost_ok ⟨hreq1, fun _ => hok1 rfl, by simp⟩
          · simp only [hint]
            exact okPost_ok ⟨hreq1, by simp, fun x hx => Or.inr (Or.inl ⟨by simpa using hx.symm,
              hok1 rfl⟩)⟩
        | Err x =>
          refine okPost_bind (okPost_of_spec
            (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) x)) ?_
          intro cf hcf
          subst hcf
          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, Std.bind_ok]
          exact okPost_ok ⟨hreq1, by simp, fun y hy => Or.inr (Or.inr (by
            simp only [core.result.Result.Err.injEq] at hy
            subst hy
            exact herr1 _ rfl))⟩


/-! ### All routes -/

/-- Every route's edges, route after route. -/
def allEdges (routes : List scene.Route) : List topology.Edge :=
  routes.flatMap (fun rt => routeEdgeList rt.cells.val)

theorem allEdges_take_succ (routes : List scene.Route) (j : Nat) (rt : scene.Route)
    (h : routes[j]? = some rt) :
    allEdges (routes.take (j + 1)) = allEdges (routes.take j) ++ routeEdgeList rt.cells.val := by
  rw [List.take_add_one, h]
  simp [allEdges, List.flatMap_append]

/-- Route `j` fails: with the list `reqj` at its entry, the route's own failure data. -/
def RoutesFail (L : scene.Layout) (pub : scene.RoutePublication) (phases next : Slice Std.I32)
    (routes : List scene.Route) (final : alloc.vec.Vec topology.Edge) (x : topology.Error)
    (j : Nat) : Prop :=
  j < routes.length ∧ ∃ rt, routes[j]? = some rt ∧ ∃ ju : Std.Usize, ju.val = j ∧
    ∃ reqj : alloc.vec.Vec topology.Edge, reqj.val = foldEdges [] (allEdges (routes.take j)) ∧
      RouteErr L pub phases next ju rt reqj final x

def RoutesLoopInv (L : scene.Layout) (pub : scene.RoutePublication) (phases next : Slice Std.I32)
    (routes : Slice scene.Route)
    (s : (alloc.vec.Vec topology.Edge) × (core.result.Result Unit topology.Error) × Std.Usize) :
    Prop :=
  RouteInv L.carrier s.1 ∧ s.2.2.val ≤ routes.val.length ∧
  (s.2.1 = core.result.Result.Ok () →
    s.1.val = foldEdges [] (allEdges (routes.val.take s.2.2.val))) ∧
  (∀ x, s.2.1 = core.result.Result.Err x → ∃ j, RoutesFail L pub phases next routes.val s.1 x j)

def RoutesLoopPost (L : scene.Layout) (pub : scene.RoutePublication) (phases next : Slice Std.I32)
    (routes : Slice scene.Route)
    (s : (core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge)) : Prop :=
  RouteInv L.carrier s.2 ∧
  (s.1 = core.result.Result.Ok () → s.2.val = foldEdges [] (allEdges routes.val)) ∧
  (∀ x, s.1 = core.result.Result.Err x → ∃ j, RoutesFail L pub phases next routes.val s.2 x j)

theorem routes_loop_body_post (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route) (hc : CarrierValid L.carrier)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize)
    (hinv : RoutesLoopInv L ⟨tree, rem, add⟩ phases next routes (req, st, r)) :
    OkPost (scene.check_routes_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add tree req st r)
      (fun y => match y with
        | .cont s' => RoutesLoopInv L ⟨tree, rem, add⟩ phases next routes
            (s'.1, s'.2.1, s'.2.2)
        | .done y => RoutesLoopPost L ⟨tree, rem, add⟩ phases next routes y) := by
  obtain ⟨hreq, hr, hok, herr⟩ := hinv
  simp only at hreq hr hok herr
  unfold scene.check_routes_loop.body
  by_cases hlt : r < Slice.len routes
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind_eq (okPost_of_spec (core.result.Result.is_ok.step_spec st)) ?_
    intro b _ hb
    cases st with
    | Err x =>
      have hbf : b = false := by simpa using hb
      subst hbf
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok ⟨hreq, fun h => by simp at h, herr⟩
    | Ok u =>
      have hbt : b = true := by simpa using hb
      subst hbt
      simp only [↓reduceIte]
      have hrlt : r.val < routes.val.length := by simpa using hlt
      refine okPost_bind (okPost_of_spec (Slice.index_usize_spec routes r hrlt)) ?_
      intro rt hrt
      have hget : routes.val[r.val]? = some rt := by
        rw [List.getElem?_eq_getElem hrlt, hrt]
      have hR : req.val = foldEdges [] (allEdges (routes.val.take r.val)) := hok rfl
      refine okPost_bind_eq (m := scene.check_route L rt r phases next ⟨tree, rem, add⟩ req)
        (scene_check_route_budget L rt r phases next ⟨tree, rem, add⟩ req hc hreq) ?_
      rintro ⟨st1, req1⟩ hcall ⟨hreq1, hok1, herr1⟩
      simp only at hreq1 hok1 herr1
      refine okPost_bind (okPost_of_spec (Usize.add_spec (x := r) (y := 1#usize) (by
        have := routes.property
        simp only [UScalar.ofNatCore_val_eq]; scalar_tac))) ?_
      intro r2 hr2
      have hr2v : r2.val = r.val + 1 := by simpa using hr2
      refine okPost_ok ?_
      refine ⟨hreq1, ?_, ?_, ?_⟩
      · show r2.val ≤ _
        omega
      · intro h
        have h' : st1 = core.result.Result.Ok () := h
        show req1.val = foldEdges [] (allEdges (routes.val.take r2.val))
        rw [hr2v, allEdges_take_succ _ _ rt hget, foldEdges_append, ← hR]
        exact hok1 h'
      · intro x hx
        have hx' : st1 = core.result.Result.Err x := hx
        exact ⟨r.val, hrlt, rt, hget, r, rfl, req, hR, herr1 x hx'⟩
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok ⟨hreq, fun h => ?_, herr⟩
    have hn : ¬ r.val < routes.val.length := by simpa using hlt
    have : r.val = routes.val.length := by omega
    rw [hok h, this, List.take_length]

theorem routes_loop_post (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route) (hc : CarrierValid L.carrier)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize)
    (hinv : RoutesLoopInv L ⟨tree, rem, add⟩ phases next routes (req, st, r)) :
    OkPost (scene.check_routes_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add req tree st r)
      (RoutesLoopPost L ⟨tree, rem, add⟩ phases next routes) := by
  unfold scene.check_routes_loop
  exact okPost_loop (fun s => RoutesLoopInv L ⟨tree, rem, add⟩ phases next routes
      (s.1, s.2.1, s.2.2))
    (RoutesLoopPost L ⟨tree, rem, add⟩ phases next routes)
    _ (by
      rintro ⟨req, st, r⟩ h
      refine okPost_mono (routes_loop_body_post L tree rem add phases next routes hc req st r h) ?_
      intro y hy
      cases y <;> exact hy)
    (req, st, r) hinv


/-- `check_routes` leaves in `required` exactly the route edges, once each, in first-occurrence
order (`foldEdges [] (allEdges routes)`); a failure is the guard (route count) or the first failing
route, cell or edge, and the list then holds the edges admitted before it. The scratch invariant
(duplicate-free, inside the carrier's edges) holds on every exit, and no exit comes from the
`required.len == carrier.edges().len` branch: an `InsufficientWorkspace` can only be the doorway's. -/
theorem scene_check_routes_required_exact (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (tree : Option spanning_tree.Tree) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (hc : CarrierValid L.carrier)
    (hinv : RouteInv L.carrier req) :
    OkPost (scene.check_routes L routes phases next tree edit req) (fun p =>
      RouteInv L.carrier p.2 ∧
      (p.1 = core.result.Result.Ok () → p.2.val = foldEdges [] (allEdges routes.val)) ∧
      (∀ x, p.1 = core.result.Result.Err x →
        (x = topology.Error.InvalidGeometry ∧ p.2 = req ∧
          routes.val.length ≠ L.circles.val.length) ∨
        ∃ j, RoutesFail L ⟨tree, edit.remove, edit.add⟩ phases next routes.val p.2 x j)) := by
  unfold scene.check_routes
  by_cases hne : (Slice.len routes != alloc.vec.Vec.len L.circles) = true
  · simp only [hne, ↓reduceIte]
    refine okPost_ok ⟨hinv, by simp, fun x hx => Or.inl ⟨?_, rfl, ?_⟩⟩
    · simpa using hx.symm
    · simpa using hne
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine okPost_bind (okPost_of_spec (vec_clear_spec alloc.alloc.Global req)) ?_
    intro req1 hreq1
    have hinv0 : RoutesLoopInv L ⟨tree, edit.remove, edit.add⟩ phases next routes
        (req1, core.result.Result.Ok (), 0#usize) := by
      refine ⟨⟨by simp [hreq1], by simp [hreq1]⟩, by simp, ?_, by simp⟩
      intro _
      simp [hreq1, allEdges]
    refine okPost_mono (routes_loop_post L tree edit.remove edit.add phases next routes hc req1
      (core.result.Result.Ok ()) 0#usize hinv0) ?_
    rintro ⟨st, req2⟩ ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => Or.inr (h3 x hx)⟩


/-- On success the scratch list is duplicate-free and holds exactly the route edges. -/
theorem scene_check_routes_ok_members (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (tree : Option spanning_tree.Tree) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (hc : CarrierValid L.carrier)
    (hinv : RouteInv L.carrier req) :
    OkPost (scene.check_routes L routes phases next tree edit req) (fun p =>
      p.1 = core.result.Result.Ok () →
        p.2.val.Nodup ∧ ∀ e, e ∈ p.2.val ↔ e ∈ allEdges routes.val) := by
  refine okPost_mono (scene_check_routes_required_exact L routes phases next tree edit req hc hinv)
    ?_
  rintro ⟨st, req'⟩ ⟨_, hok, _⟩ h
  have h' := hok h
  refine ⟨by rw [h']; exact foldEdges_nodup _ _ List.nodup_nil, fun e => ?_⟩
  rw [h', foldEdges_mem]
  simp

end Labyrinth
