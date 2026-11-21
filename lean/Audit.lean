import LabyrinthCore.Spec
import LabyrinthCore.ConstructorTreeInterpretation
import LabyrinthCore.MutationRerootSpec
import LabyrinthCore.ConstructorCarrierEdges
import LabyrinthCore.ConstructorDepthFirstTree
import LabyrinthCore.MutationEditEdges
import LabyrinthCore.ConstructorQuotientDFS
import LabyrinthCore.MutationTrace
import LabyrinthCore.ConstructorSceneExpandedCarrier
import LabyrinthCore.ConstructorOrientation
import LabyrinthCore.ConstructorSceneRejection
import LabyrinthCore.ConstructorSceneAcceptance
import LabyrinthCore.ConstructorSceneTotal
import LabyrinthCore.SceneStd
import LabyrinthCore.ScenePublication

#print axioms set_parent_spec
#print axioms Labyrinth.constructor_parentGraph_adj_iff
#print axioms Labyrinth.constructor_rooted_connected
#print axioms Labyrinth.constructor_rooted_isTree
#print axioms Labyrinth.constructor_treeValid_isTree
#print axioms Labyrinth.mutation_reroot_success
#print axioms Labyrinth.mutation_reroot_preserves
#print axioms Labyrinth.constructor_carrier_from_csr_spec
#print axioms Labyrinth.constructor_carrier_from_csr_accepts
#print axioms Labyrinth.constructor_carrier_from_edges_total_spec
#print axioms Labyrinth.constructor_carrier_from_edges_accepts
#print axioms Labyrinth.constructor_depth_first_accepts
#print axioms Labyrinth.constructor_tree_dfs_accepts
#print axioms Labyrinth.constructor_tree_dfs_invalid_root
#print axioms Labyrinth.constructor_tree_dfs_insufficient_workspace
#print axioms Labyrinth.constructor_tree_dfs_spec
#print axioms Labyrinth.mutation_edit_edges_total_frame
#print axioms Labyrinth.constructor_quotient_depth_first_accepts
#print axioms Labyrinth.mutation_edit_edges_tree_valid
#print axioms Labyrinth.mutation_exchange_tree_valid
#print axioms Labyrinth.mutation_operation_preserves
#print axioms Labyrinth.mutation_accepted_trace_prefix_valid
#print axioms Labyrinth.mutation_edit_edges_preserves_disjoint
#print axioms Labyrinth.constructor_scene_expanded_carrier_accepts
#print axioms Labyrinth.constructor_scene_orientation_accepts
#print axioms Labyrinth.constructor_scene_rejects_invalid_forest
#print axioms Labyrinth.constructor_scene_publish_accepts
#print axioms Labyrinth.constructor_scene_quotient_prefix_total
#print axioms Labyrinth.constructor_scene_quotient_prefix_accepts
#print axioms Labyrinth.constructor_scene_capture
#print axioms Labyrinth.constructor_scene_after_prefix_total
#print axioms Labyrinth.constructor_scene_dfs_guarded
#print axioms Labyrinth.constructor_scene_dfs_accepts
#print axioms Labyrinth.constructor_scene_dfs_spec
#print axioms core.num.I32.rem_euclid
#print axioms core.num.I32.abs
#print axioms core.ops.range.RangeInclusive.contains
#print axioms core.option.Option.Insts.CoreFmtDebug.fmt
#print axioms core.option.OptionShared0T.copied
#print axioms core.option.Option.Insts.CoreCloneClone.clone
#print axioms core.option.Option.Insts.CoreCmpPartialEqOption.eq
#print axioms alloc.vec.Vec.clear
#print axioms Aeneas.Std.I32.div
#print axioms Labyrinth.i32_abs_spec
#print axioms Labyrinth.i32_rem_euclid_spec
#print axioms Labyrinth.range_inclusive_contains_i32_spec
#print axioms Labyrinth.range_inclusive_contains_i32_new
#print axioms Labyrinth.option_copied
#print axioms Labyrinth.option_clone_i32
#print axioms Labyrinth.option_clone_u64
#print axioms Labyrinth.option_clone_usize
#print axioms Labyrinth.option_eq_spec
#print axioms Labyrinth.option_eq_i32_spec
#print axioms Labyrinth.option_eq_u64_spec
#print axioms Labyrinth.option_eq_usize_spec
#print axioms Labyrinth.vec_clear_spec
#print axioms Labyrinth.i32_div_spec
#print axioms Labyrinth.i32_div_turn_eight
#print axioms Labyrinth.i32_div_turn_four
#print axioms Labyrinth.option_debug_fmt_none
#print axioms Labyrinth.option_debug_fmt_some
#print axioms Labyrinth.slice_contains_spec
#print axioms Labyrinth.edge_eq_spec
#print axioms Labyrinth.slice_contains_edge_spec
#print axioms Labyrinth.option_ok_or_spec
#print axioms Labyrinth.option_ok_or_is_ok
#print axioms Labyrinth.result_is_err_spec
#print axioms Labyrinth.lax_admissible
#print axioms Labyrinth.lax_of_ok_imp
#print axioms Labyrinth.lax_of_ok
#print axioms Labyrinth.loop_lax
#print axioms Labyrinth.lax_bind
#print axioms Labyrinth.lax_triv
#print axioms Labyrinth.lax_ok
#print axioms Labyrinth.check_stamp_stale_epoch
#print axioms Labyrinth.check_stamp_stale_revision
#print axioms Labyrinth.check_stamp_overflow
#print axioms Labyrinth.check_stamp_ok
#print axioms Labyrinth.check_stamp_spec
#print axioms Labyrinth.stamp_rejects_of_accepts
#print axioms Labyrinth.stamp_gate
#print axioms Labyrinth.suspend_spec
#print axioms Labyrinth.resume_spec
#print axioms Labyrinth.u64_checked_succ
#print axioms Labyrinth.request_layout_spec
#print axioms Labyrinth.publish_layout_loop_spec
#print axioms Labyrinth.publish_layout_spec
#print axioms Labyrinth.spec_eq_ok
#print axioms Labyrinth.pending_ne_eval
#print axioms Labyrinth.reject_layout_stale_pending
#print axioms Labyrinth.reject_layout_stale_latest
#print axioms Labyrinth.reject_layout_invalid_viewport
#print axioms Labyrinth.reject_layout_overflow
#print axioms Labyrinth.reject_layout_scan_failed
#print axioms Labyrinth.reject_layout_commit
#print axioms Labyrinth.tick_stale_epoch
#print axioms Labyrinth.tick_stale_revision
#print axioms Labyrinth.tick_revision_overflow
#print axioms Labyrinth.tick_wall_regressed
#print axioms Labyrinth.tick_frozen
#print axioms Labyrinth.tick_reanchored
#print axioms Labyrinth.tick_clock_overflow
#print axioms Labyrinth.drain_patches_loop0_frame
#print axioms Labyrinth.drain_patches_frame
#print axioms Labyrinth.tick_loop1_frame
#print axioms Labyrinth.tick_active_lax
#print axioms Labyrinth.tick_active
