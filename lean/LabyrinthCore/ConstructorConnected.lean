module
public import LabyrinthCore.ConstructorConnectivity
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The arrays actually allocated by `from_csr` satisfy the singleton-root search invariant. -/
theorem constructor_connectivity_initial_state
    (offsets neighbors : alloc.vec.Vec Usize) (n : Usize)
    (seen : alloc.vec.Vec Bool) (stack : alloc.vec.Vec Usize)
    (hn : n.val = offsets.val.length - 1) (hpositive : 0 < n.val)
    (hseen : seen.val = List.replicate n.val false)
    (hstack : stack.val = List.replicate n.val 0#usize) :
    constructorSearchState (offsets.val.length - 1) (constructorCsrAdjacent offsets neighbors)
      (seen.set 0#usize true) stack 1#usize 1#usize none {0} := by
  refine {
    seen_length := by simp [hseen, hn]
    stack_length := by simp [hstack, hn]
    depth_le := le_rfl
    reached_eq := by simp
    bounded := ?_
    root_mem := by simp
    seen_eq := ?_
    pending := ?_
    reachable := ?_
    covered := ?_
  }
  · intro v hv
    have he : v = 0 := by simpa only [Finset.mem_singleton] using hv
    subst v
    exact Finset.mem_range.mpr (by omega)
  · intro v hv
    by_cases he : v = 0
    · subst v
      simp [alloc.vec.Vec.set, hseen, hpositive]
    · have hvn : v < n.val := by omega
      simp [alloc.vec.Vec.set, hseen, he, Ne.symm he, hvn]
  · intro i hi
    have he : i = 0 := by simpa using hi
    subst i
    exact ⟨0#usize, by simp [hstack, hpositive], by simp⟩
  · intro v hv
    have he : v = 0 := by simpa only [Finset.mem_singleton] using hv
    subst v
    exact Relation.ReflTransGen.refl
  · intro v hv
    have he : v = 0 := by simpa only [Finset.mem_singleton] using hv
    subst v
    exact Or.inr (Or.inr ⟨0, by simp, 0#usize, by simp [hstack, hpositive], rfl⟩)

/-- The complete generated CSR connectivity phase accepts exactly connected input,
starting from its real allocation/marking state rather than a caller-supplied invariant. -/
theorem constructor_csr_connectivity_accepts
    (offsets neighbors : alloc.vec.Vec Usize) (n unused : Usize)
    (seen : alloc.vec.Vec Bool) (stack : alloc.vec.Vec Usize)
    (hn : n.val = offsets.val.length - 1) (hpositive : 0 < n.val)
    (hseen : seen.val = List.replicate n.val false)
    (hstack : stack.val = List.replicate n.val 0#usize)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hentries : constructorAllRows offsets neighbors (offsets.val.length - 1)) :
    WP.spec (topology.Carrier.from_csr_loop2 offsets neighbors unused
      (seen.set 0#usize true) stack 1#usize 1#usize) (fun result =>
        result.val ≤ n.val ∧ (result = n ↔ ∀ v, v < n.val →
          Relation.ReflTransGen (constructorCsrAdjacent offsets neighbors) 0 v)) := by
  apply WP.spec_mono (constructor_connectivity_spec offsets neighbors unused
    (seen.set 0#usize true) stack 1#usize 1#usize {0} hrows hentries
    (constructor_connectivity_initial_state offsets neighbors n seen stack hn hpositive hseen hstack))
  intro result hresult
  simpa only [hn, UScalar.eq_equiv] using hresult

end Labyrinth
