module
public import LabyrinthCore.ConstructorDFSLoop
public import LabyrinthCore.ConstructorInitialize
public import LabyrinthCore.Mutations
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The actual cyclic DFS terminates and constructs a ranked rooted tree on raw directed CSR.
The incoming witnesses are original slots, so quotient parallel edges remain distinguishable. -/
theorem constructor_depth_first_accepts {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets neighbors : Slice Usize)
    (root : Usize) (rng : R) (work : spanning_tree.Workspace)
    (hinput : ConstructorDFSInput offsets neighbors root.val)
    (hvalid : WorkspaceValid work)
    (hcapacity : constructorDFSVertexCount offsets ≤ work.path.val.length) :
    WP.spec (spanning_tree.depth_first adapter offsets neighbors root rng work)
      (fun output => output.1 = .Ok () ∧
        ConstructorDFSOutput offsets neighbors root work output.2.2) := by
  have hnonempty : 0 < offsets.val.length := by
    have h := hinput.nonempty
    unfold constructorDFSVertexCount at h
    omega
  unfold spanning_tree.depth_first
  apply WP.spec_bind (Usize.sub_spec (x := Slice.len offsets) (y := 1#usize)
    (by simpa using Nat.succ_le_of_lt hnonempty))
  intro n hn
  have hnval : n.val = constructorDFSVertexCount offsets := by
    simpa only [Slice.len_val, UScalar.ofNatCore_val_eq, constructorDFSVertexCount] using hn.1
  apply WP.spec_bind (mutation_clear_edits_total work hvalid)
  intro cleared hclear
  obtain ⟨hcvalid, _hccount, _hcseen, _hcframes, hcpath, _hcparents, _hcincoming,
    _hcnodes, hcedges, _hcslots⟩ := hclear
  apply WP.spec_bind (constructor_dfs_initialize_spec root n cleared hcvalid (by
    rw [hnval, hcpath]
    exact hcapacity))
  intro initialized hinit
  obtain ⟨hivalid, hipath, _hiframes, _hislots, _hinodes, _hicount, hiedges, hiprefix, _hisuffix⟩ := hinit
  have hpath : initialized.path = work.path := hipath.trans hcpath
  have hedges : initialized.edge_capacity = work.edge_capacity := hiedges.trans hcedges
  obtain ⟨lo, hi, hlo, hhi, hloval, hhival⟩ := constructor_dfs_row_lookup offsets root hinput.root_lt
  have hrootOffset : root.val + 1 < offsets.val.length := by
    have h := hinput.root_lt
    unfold constructorDFSVertexCount at h
    omega
  have hordered : lo.val ≤ hi.val := by rw [hloval, hhival]; exact hinput.ordered _ hinput.root_lt
  apply WP.spec_bind (constructor_enter_spec adapter hrng offsets root lo hi rng
    hrootOffset hlo hhi hordered)
  rintro ⟨status, rng'⟩ ⟨frame, hstatus, hcell, hremaining, _hempty, hnext⟩
  dsimp only at hstatus
  rw [hstatus]
  dsimp only
  have hbranch : WP.spec
      (core.result.Result.Insts.CoreOpsTry.branch
        (core.result.Result.Ok frame :
          core.result.Result spanning_tree.Frame topology.Error))
      (fun cf => cf = .Continue frame) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hbranch
  intro cf hcf
  subst cf
  dsimp only
  simp only [alloc.vec.Vec.index_mut_slice_index]
  have hframes : initialized.frames.val.length = work.path.val.length := by
    rw [hivalid.2.1, hpath]
  have hseen : initialized.seen.val.length = work.path.val.length := by rw [hivalid.1, hpath]
  have hparents : initialized.parents.val.length = work.path.val.length := by rw [hivalid.2.2.1, hpath]
  have hincoming : initialized.incoming.val.length = work.path.val.length := by rw [hivalid.2.2.2.1, hpath]
  have hcapPos : 0 < work.path.val.length := by have := hinput.nonempty; omega
  have hrootSeen : root.val < initialized.seen.val.length := by rw [hseen]; have := hinput.root_lt; omega
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec initialized.frames 0#usize (by
    simpa only [UScalar.ofNatCore_val_eq, hframes] using hcapPos))
  rintro ⟨oldFrame, backFrame⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec initialized.seen root hrootSeen)
  rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
  have hframeValid : ConstructorDFSFrameValid offsets frame := by
    refine ⟨by simpa only [hcell] using hinput.root_lt, ?_, ?_⟩
    · rw [hcell, hremaining, hloval, hhival]
    · intro hp
      have hlt : lo.val < hi.val := by omega
      simpa only [hcell, hloval, hhival] using hnext hlt
  have hrem : frame.remaining.val = constructorDFSOffset offsets (root.val + 1) -
      constructorDFSOffset offsets root.val := by simpa only [hloval, hhival] using hremaining
  have hstart := constructor_dfs_invariant_initial offsets neighbors root work.path.val.length
    initialized.seen initialized.frames initialized.parents initialized.incoming frame hinput
    hseen hframes hparents hincoming hcapacity
    (fun v hv => (hiprefix v (by rw [hnval]; exact hv)).1)
    (hiprefix root.val (by rw [hnval]; exact hinput.root_lt)).2.1 hcell hframeValid hrem
  apply WP.spec_bind (constructor_dfs_loop_spec adapter hrng offsets neighbors root.val
    work.path.val.length hinput rng' (initialized.seen.set root true)
    (initialized.frames.set 0#usize frame) initialized.parents initialized.incoming 1#usize 1#usize
    {root.val} (fun _ => 0) (by simpa only [UScalar.ofNatCore_val_eq] using hstart))
  rintro ⟨rng'', seen, frames, parents, incoming, reached, status⟩ ⟨hstatus, visited, rank, hfinal⟩
  rw [hstatus]
  have hloopBranch : WP.spec
      (core.result.Result.Insts.CoreOpsTry.branch
        (core.result.Result.Ok () : core.result.Result Unit topology.Error))
      (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hloopBranch
  intro loopCf hloopCf
  subst loopCf
  dsimp only
  obtain ⟨_hvisited, hreached, hall⟩ := constructor_dfs_stack_empty_all_seen hinput hfinal
  have heq : reached = n := (UScalar.eq_equiv _ _).mpr (hreached.trans hnval.symm)
  simp only [heq, bne_self_eq_false, Bool.false_eq_true, ite_false]
  apply (WP.spec_ok _).mpr
  refine ⟨rfl, ?_⟩
  refine {
    valid := ?_
    path := hpath
    edge_capacity := hedges
    discovered := hall
    tree := ?_
    incoming := ?_ }
  · change seen.val.length = initialized.path.val.length ∧
      frames.val.length = initialized.path.val.length ∧
      parents.val.length = initialized.path.val.length ∧
      incoming.val.length = initialized.path.val.length ∧ _
    rw [hpath]
    exact ⟨hfinal.seen_length, hfinal.frames_length, hfinal.parents_length,
      hfinal.incoming_length, by simpa only [hpath] using hivalid.2.2.2.2⟩
  · exact constructor_dfs_invariant_rooted hinput hfinal
      (fun v hv => (hfinal.seen_iff v hv).mp (hall v hv))
  · intro v hv hne
    exact hfinal.witness v ((hfinal.seen_iff v hv).mp (hall v hv)) hne

end Labyrinth
