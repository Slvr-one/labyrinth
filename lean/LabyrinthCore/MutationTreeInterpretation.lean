module
public import LabyrinthCore.Mutations
public import LabyrinthCore.ConstructorTreeInterpretation
public import Mathlib.Data.Fintype.Card

public section

namespace Labyrinth

 theorem mutation_first_root_before_size (p : List Nat) (root v : Nat)
    (hp : ∀ x ∈ p, x < p.length) (hv : v < p.length)
    (hexists : ∃ k, follow p k v = root) :
    ∃ k, k < p.length ∧ follow p k v = root := by
  classical
  let k := Nat.find hexists
  have hk : follow p k v = root := Nat.find_spec hexists
  have hdistinct : ∀ i j, i < j → j ≤ k → follow p i v ≠ follow p j v := by
    intro i j hij hj heq
    have hearlier : follow p (k - j + i) v = root := by
      rw [mutation_follow_add, heq, ← mutation_follow_add, Nat.sub_add_cancel hj]
      exact hk
    have hmin : k ≤ k - j + i := Nat.find_min' hexists hearlier
    omega
  let f : Fin (k + 1) → Fin p.length := fun i =>
    ⟨follow p i.val v, mutation_follow_bound p hp i.val v hv⟩
  have hinjective : Function.Injective f := by
    intro a b hab
    have hvals : follow p a.val v = follow p b.val v := congrArg Fin.val hab
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hdistinct a.val b.val hlt (by omega) hvals
    · exact hdistinct b.val a.val hgt (by omega) hvals.symm
  have hcard := Fintype.card_le_of_injective f hinjective
  have hklt : k < p.length := by simpa using hcard
  exact ⟨k, hklt, hk⟩

 theorem mutation_reachable_root_bounded (p : List Nat) (root v : Nat)
    (hp : ∀ x ∈ p, x < p.length) (hv : v < p.length)
    (hr : parentAt p root = root)
    (hexists : ∃ k, follow p k v = root) :
    follow p p.length v = root := by
  obtain ⟨k, hk, hreach⟩ := mutation_first_root_before_size p root v hp hv hexists
  have hlen : p.length = (p.length - k) + k := by omega
  rw [hlen, mutation_follow_add, hreach]
  exact mutation_follow_fixed p root hr _

 theorem mutation_connected_rooted (p : List Nat) (root : Nat)
    (hrange : root < p.length) (hroot : p[root]? = some root)
    (hp : ∀ x ∈ p, x < p.length)
    (hconnected : (constructorParentGraph p).Connected) : RootedTree p root := by
  have hfixed : parentAt p root = root := by simp [parentAt, hroot]
  let reaches : Fin p.length → Prop := fun v => ∃ k, follow p k v.val = root
  have hclosed : ∀ {u v : Fin p.length}, (constructorParentGraph p).Adj u v →
      reaches u → reaches v := by
    intro u v hadj hu
    obtain ⟨_, hparent | hparent⟩ := hadj
    · obtain ⟨k, hk⟩ := hu
      cases k with
      | zero =>
        have huRoot : u.val = root := hk
        have hvRoot : v.val = root := by
          rw [huRoot, hfixed] at hparent
          exact hparent.symm
        exact ⟨0, hvRoot⟩
      | succ k =>
        exact ⟨k, by simpa only [follow, hparent] using hk⟩
    · obtain ⟨k, hk⟩ := hu
      exact ⟨k + 1, by simpa only [follow, hparent] using hk⟩
  have hwalk : ∀ {u v : Fin p.length}, (constructorParentGraph p).Walk u v →
      reaches u → reaches v := by
    intro u v walk
    induction walk with
    | nil => exact id
    | cons hadj walk ih => exact fun hu => ih (hclosed hadj hu)
  refine ⟨hrange, hroot, hp, ?_⟩
  intro v hv
  obtain ⟨walk⟩ := hconnected (⟨root, hrange⟩ : Fin p.length) ⟨v, hv⟩
  have hreach : reaches ⟨v, hv⟩ := hwalk walk ⟨0, rfl⟩
  exact mutation_reachable_root_bounded p root v hp hv hfixed hreach

end Labyrinth
