module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The adapter must terminate and return a legal choice on every positive request. -/
def constructorLegalRng {R : Type*} (adapter : tree.Rng R) : Prop :=
  ∀ (state : R) (bound : Usize), 0 < bound.val →
    WP.spec (adapter.next_below state bound) (fun pair => pair.1.val < bound.val)

/-- Entering an actual DFS frame chooses a legal cyclic start and preserves an empty row's RNG. -/
theorem constructor_enter_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets : Slice Usize)
    (cell lo hi : Usize) (rng : R)
    (hcell : cell.val + 1 < offsets.val.length)
    (hlo : offsets.val[cell.val]? = some lo)
    (hhi : offsets.val[cell.val + 1]? = some hi)
    (hordered : lo.val ≤ hi.val) :
    WP.spec (spanning_tree.enter adapter offsets cell rng) (fun result =>
      ∃ frame, result.1 = .Ok frame ∧ frame.cell = cell ∧
        frame.remaining.val = hi.val - lo.val ∧
        (lo.val = hi.val → frame.next = lo ∧ result.2 = rng) ∧
        (lo.val < hi.val → lo.val ≤ frame.next.val ∧ frame.next.val < hi.val)) := by
  unfold spanning_tree.enter
  apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
    have := offsets.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro next hnext
  have hn : next.val = cell.val + 1 := by simpa using hnext
  apply WP.spec_bind (Slice.index_usize_spec offsets next (by
    change next.val < offsets.val.length
    omega))
  intro rowEnd hend
  have he : rowEnd = hi := by
    have hg : offsets.val[next.val]? = some rowEnd := by
      rw [List.getElem?_eq_getElem (show next.val < offsets.val.length by omega), hend]
    rw [hn, hhi] at hg
    exact Option.some.inj hg.symm
  rw [he]
  apply WP.spec_bind (Slice.index_usize_spec offsets cell (by
    change cell.val < offsets.val.length
    omega))
  intro rowStart hstart
  have hs : rowStart = lo := by
    have hg : offsets.val[cell.val]? = some rowStart := by
      rw [List.getElem?_eq_getElem (show cell.val < offsets.val.length by omega), hstart]
    rw [hlo] at hg
    exact Option.some.inj hg.symm
  rw [hs]
  apply WP.spec_bind (Usize.sub_spec (x := hi) (y := lo) hordered)
  intro degree hd
  by_cases hdegree : degree > 0#usize
  · simp only [hdegree, ite_true]
    have hpositive : 0 < degree.val := by simpa using hdegree
    apply WP.spec_bind (hrng rng degree hpositive)
    rintro ⟨choice, rng'⟩ hchoice
    dsimp only at hchoice ⊢
    have hlegal : ¬ choice ≥ degree := by simpa using hchoice
    change WP.spec
      (if choice ≥ degree then ok (core.result.Result.Err topology.Error.InvalidChoice, rng')
       else do
         let cyclicStart ← lo + choice
         ok (core.result.Result.Ok
           ({ cell := cell, next := cyclicStart, remaining := degree } : spanning_tree.Frame), rng')) _
    simp only [hlegal, ite_false]
    apply WP.spec_bind (Usize.add_spec (x := lo) (y := choice) (by
      have hmax : hi.val ≤ Usize.max := by scalar_tac
      omega))
    intro cyclicStart hcyclic
    apply (WP.spec_ok _).mpr
    refine ⟨_, rfl, rfl, hd.1, (fun heq => by omega), ?_⟩
    intro _
    change lo.val ≤ cyclicStart.val ∧ cyclicStart.val < hi.val
    constructor <;> omega
  · simp only [hdegree, ite_false]
    have hz : degree.val = 0 := by
      have : ¬ 0 < degree.val := by simpa using hdegree
      omega
    apply (WP.spec_ok _).mpr
    exact ⟨_, rfl, rfl, hd.1, (fun _ => ⟨rfl, rfl⟩), fun hlt => by omega⟩

/-- Discovery ranks provide a noncircular invariant for constructing the shared parent tree. -/
theorem constructor_rooted_of_discovery_rank (p : List Nat) (root : Nat)
    (rank : Nat → Nat)
    (hroot : root < p.length) (hfixed : p[root]? = some root)
    (hbounded : ∀ v ∈ p, v < p.length)
    (hrank : ∀ v, v < p.length → rank v < p.length)
    (hdecreases : ∀ v, v < p.length → v ≠ root → rank (parentAt p v) < rank v) :
    RootedTree p root := by
  have hpbounded (v : Nat) (hv : v < p.length) : parentAt p v < p.length := by
    apply hbounded
    simp only [parentAt, List.getElem?_eq_getElem hv, Option.getD_some]
    exact List.getElem_mem hv
  have hrootParent : parentAt p root = root := by simp only [parentAt, hfixed, Option.getD_some]
  have hrootFollow (k : Nat) : follow p k root = root := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [follow, hrootParent] using ih
  have hreach : ∀ k v, v < p.length → rank v < k → follow p k v = root := by
    intro k
    induction k with
    | zero => intro v hv hrv; omega
    | succ k ih =>
      intro v hv hrv
      by_cases he : v = root
      · subst v
        exact hrootFollow (k + 1)
      · exact ih (parentAt p v) (hpbounded v hv) (by have := hdecreases v hv he; omega)
  exact ⟨hroot, hfixed, hbounded, fun v hv => hreach p.length v hv (hrank v hv)⟩

end Labyrinth
