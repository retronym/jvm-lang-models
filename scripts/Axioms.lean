import Zinc
import Scala
import Links.ZincBridgeScala3
import Links.ZincBridgeKeys
import Links.ZincBridgeLibs
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
