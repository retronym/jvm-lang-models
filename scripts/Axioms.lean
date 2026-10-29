import Zinc
import Scala
import Links.ZincBridgeScala3
import Links.ZincBridgeKeys
import Links.ZincBridgeLibs
import Query.Lazy
import Query.Freeze
import Query.Interrupt
import Query.Revision
import Query.Concurrent
import Query.Roots
import Query.WaitGraph
import Query.Victim
import Query.Regime
import Query.Publication
import ScalaTypes.Laziness
import ScalaTypes.Scopes
import ScalaTypes.Fusion
import ScalaTypes.ToyTree
import ScalaTypes.ToyBodyEdit
/-! The core theorems' axioms, checked by `scripts/check_axioms.py`: only `propext`,
`Classical.choice` and `Quot.sound` are allowed (no `sorryAx`, no `Lean.ofReduceBool` from
`native_decide`). -/

-- T1
#print axioms Query.Task.run_eq_of_trace
-- T2, T3a, per framework variant
#print axioms IncComp.Compiler.round_preserves
#print axioms IncComp.Compiler.zinc_sound
#print axioms IncComp.GCompiler.round_preserves
#print axioms IncComp.TCompiler.round_preserves
#print axioms IncComp.TCompiler.zinc_sound
#print axioms IncComp.NCompiler.round_preserves
#print axioms IncComp.NCompiler.zinc_sound
-- T3b, T3
#print axioms IncComp.Compiler.fixpoint_unique_of_wf
#print axioms IncComp.Compiler.fixpoint_unique_of_explicit
#print axioms IncComp.Compiler.zinc_eq_clean_of_wf
#print axioms IncComp.Compiler.zinc_eq_clean_of_explicit
-- T4
#print axioms IncComp.Compiler.zinc_some_of_monotoneFrom
#print axioms IncComp.Compiler.zinc_some_of_explicit
#print axioms IncComp.Compiler.zinc_some_of_wf
-- T5
#print axioms IncComp.NCompiler.downstream_sound
-- proved counterexamples that used to lean on native_decide
#print axioms Zinc.PingPong.zinc_diverges
#print axioms IncComp.Stale.stale_unsound
#print axioms IncComp.Stale.stale_affected
-- the instances' soundness theorems and witnesses
#print axioms Zinc.JavaSpec.fix_sound
#print axioms Zinc.JavaSealedSpec.fix_sound
#print axioms Zinc.JavaOrder.mixed_sound
#print axioms Zinc.SplitProof.Spec.cross_downstream_sound
#print axioms Zinc.SplitProof.Spec.global_obligations
#print axioms Zinc.SplitProof.Spec.narrowed_obligations
#print axioms Zinc.SplitProof.Spec.joint_not_comp
#print axioms Zinc.Cycles.zinc_ne_clean
#print axioms Zinc.Cycles.annotated_eq_clean
#print axioms Zinc.Annotations.fix_sound
#print axioms Zinc.HashForms.conservative_sound
#print axioms Zinc.Naming.Mini.spelling_bugs
#print axioms Zinc.PipelineLifecycle.rollback_preserves
#print axioms Zinc.Synthetic.sound_of_agree
#print axioms Zinc.InlineOpaqueSpec.fix_sound
#print axioms Zinc.InlineOpaqueSound.denot_sound
#print axioms Zinc.MacroDeps.fix_sound
#print axioms Zinc.MacroDeps.Ex.private_today
#print axioms Zinc.Erasure.dep_sound
#print axioms Zinc.ImplicitScope.is_sound
#print axioms Zinc.Flat.flat_sound
#print axioms Zinc.Hier.D_obligations
#print axioms Zinc.Hier.W_obligations
#print axioms Zinc.Hier.Mk_obligations
-- the general form (General.lean), where T2, T3a, T4 (monotone) and T5 are proved once
#print axioms IncComp.XCompiler.round_preserves
#print axioms IncComp.XCompiler.zinc_sound
#print axioms IncComp.XCompiler.zinc_some_of_monotoneFrom
#print axioms IncComp.XCompiler.downstream_sound
-- T3 for keys from the tree, through the forgetful map
#print axioms IncComp.TCompiler.zinc_eq_clean_of_explicit
#print axioms Zinc.SplitProof.Spec.g_global_obligations
#print axioms Zinc.SplitProof.Spec.g_narrowed_obligations
#print axioms Zinc.SplitProof.Spec.g12_today
#print axioms IncComp.TCompiler.downstream_sound
-- the shared asSeenFrom (packages/scala-types/ScalaTypes/AsSeenFrom.lean) and T1 for lowering
#print axioms AsSeenFrom.compose
#print axioms AsSeenFrom.chain_is_single
#print axioms Scala.lower_congr
-- B4 (Track B4) and its extensions
#print axioms IncComp.XCompiler.untouched_eq_clean
-- precision (phase 30)
#print axioms IncComp.XCompiler.necessary_invalidated
#print axioms IncComp.XCompiler.policyOver_mono
#print axioms Links.ZincBridge.gap_witness
#print axioms Links.ZincBridgeScala3.not_comp
#print axioms Links.ZincBridgeScala3.after_eq_fresh_fix
#print axioms Links.ZincBridgeKeys.coverage_fails
#print axioms Links.ZincBridgeKeys.loop_witness
#print axioms Links.ZincBridgeLibs.library_client
-- files as a layer
#print axioms IncComp.XCompiler.round_preserves_charged
#print axioms IncComp.XCompiler.zinc_sound_charged
#print axioms Zinc.FileSpec.today_not_charged
#print axioms Zinc.FileSpec.every_obligations
#print axioms Zinc.Fi.fi_not_covered
#print axioms Zinc.Fi.fi_loop
#print axioms IncComp.XCompiler.downstream_sound_charged
#print axioms Zinc.Fi.fi_loop_kept
#print axioms Zinc.Fi.kept_obligations
#print axioms Zinc.Fi.kept_sound
-- SAM conversion and local classes
#print axioms Zinc.Sam.fix_sound
#print axioms Zinc.Sam.today_sound_argFree
-- The shared walk (Phase 29): over headers it is the walk over declarations, and Hier's lookup is it
#print axioms Query.Task.trace_interp
#print axioms Scala.lookupH_eq
#print axioms Scala.asks_lookupH
#print axioms Zinc.Hier.Shared.toy_eq_shared
#print axioms Zinc.Flat.Fl_obligations
#print axioms Zinc.Flat.Shared.lin_eq_shared
#print axioms Zinc.Flat.Shared.sel_eq_shared
#print axioms Scala.asks_linWith_chain
#print axioms Scala.linWith_chain
#print axioms Zinc.Erasure.Er_obligations
-- Track T: the model of the compilers' checks, and what the accepted programs do when run
#print axioms Scala.Paths.calibrated
#print axioms Scala.Paths.accepted_sound_except
#print axioms Scala.Paths.nulls_no_cce
#print axioms Scala.Paths.unsound_counts
-- Track L: laziness
#print axioms Query.Lazy.force_ok
#print axioms Query.Lazy.forceAll_ok
#print axioms Query.Lazy.cycle_unranked
#print axioms Query.Lazy.phase_ranked
#print axioms Query.Freeze.guarded_quasi_det
#print axioms ScalaTypes.Laziness.scalac5_unranked
#print axioms ScalaTypes.Laziness.implI_unranked
#print axioms ScalaTypes.Laziness.implicitSkip_separate
#print axioms ScalaTypes.Laziness.exportOrder_reads_differ
#print axioms ScalaTypes.Scopes.late_eq_truth_iff
#print axioms ScalaTypes.Scopes.enteredAfter_sound
#print axioms ScalaTypes.Scopes.lifted_unsound
#print axioms ScalaTypes.Fusion.fused_eq_seq_of_relabel
#print axioms ScalaTypes.Scopes.flatname_guarded
-- Track I: interruptibility
#print axioms Query.Interrupt.forceA_agree
#print axioms Query.Interrupt.abort_restart_ok
#print axioms Query.Interrupt.forceA_unlock_touched
#print axioms Query.Interrupt.abort_touched
#print axioms Query.Interrupt.nested_empty_stack_reorders
#print axioms Query.Interrupt.nested_inside_frame_cycles
#print axioms Query.Interrupt.forcePeek_ok
#print axioms Query.Interrupt.forceT_agree
#print axioms Query.Interrupt.psi_root_order_dependent
#print axioms Query.Interrupt.consuming_add_one_owner
#print axioms Query.Interrupt.keep_cache_sound
#print axioms ScalaTypes.Laziness.implicitSkip_taint_rejects
-- Track I: two forcers
#print axioms Query.Concurrent.run_agree
#print axioms Query.Concurrent.run_ranked_no_cyc
#print axioms Query.Concurrent.waitCycle_unranked
#print axioms Query.Concurrent.cross_cycle_both_report
#print axioms Query.Concurrent.peek_any_races
#print axioms Query.Concurrent.peek_own_agrees
#print axioms Query.Concurrent.abort_waiter_takes_over
#print axioms Query.Concurrent.abort_keep_hole_waiter_stuck
-- Track I: the multi-reader design as built
#print axioms Query.Roots.run_agree
#print axioms Query.Roots.run_ranked_no_cyc
#print axioms Query.Roots.depCycle_unranked
#print axioms Query.Roots.lock_order_false_cycle
#print axioms Query.Roots.lock_order_refine_ok
#print axioms Query.Roots.peekBoth_report_false_cycle
#print axioms Query.Roots.peekBoth_yield_sequential
#print axioms Query.WaitGraph.release_window_false_chain
#print axioms Query.WaitGraph.edge_check_sound
#print axioms Query.Victim.livelock_forever
#print axioms Query.Victim.backoff_progress
#print axioms Query.Victim.raised_implies_depCycle
#print axioms Query.Regime.done_one_version
#print axioms Query.Publication.stamped_whole
#print axioms Query.Publication.fields_valueFirst_weak_torn
#print axioms Query.Publication.clear_loses_invalidation
#print axioms ScalaTypes.ToyBodyEdit.rulesOf_erase
#print axioms ScalaTypes.ToyBodyEdit.bodyEdit_kept_run_sound
-- Track I: revisions
#print axioms Query.Revision.reuse_sound
#print axioms Query.Revision.session_eq_fresh
-- Track I: the namer and the kernel
#print axioms ScalaTypes.ToyNamer.l9_dotc_order_dependent
#print axioms ScalaTypes.ToyNamer.l2_dotc_order_dependent
#print axioms ScalaTypes.ToyKernel.results_before_after_proposed
-- Track I: trees
#print axioms ScalaTypes.ToyTree.targeted_eq_whole
#print axioms ScalaTypes.ToyTree.tier1_body_edit
#print axioms ScalaTypes.ToyTree.tier3b_scope_member
#print axioms ScalaTypes.ToyTree.big_session
