# The framework, merged

## Problem

The framework exists in four copies:

| Variant | Answers and hash read | Keys from | Extras |
|---|---|---|---|
| `Compiler` (`Model.lean`) | one unit's interface | the trace | |
| [`GCompiler`](../IncComp/NonLocal.lean#L25) ([`NonLocal.lean`](../IncComp/NonLocal.lean)) | answers one unit; hash several (`hashDeps`) | the trace | closure keys whose `covers` depends on the interfaces |
| [`TCompiler`](../IncComp/Tree.lean#L24) ([`Tree.lean`](../IncComp/Tree.lean)) | one unit's interface | the output | |
| [`NCompiler`](../IncComp/NonLocalAns.lean#L32) ([`NonLocalAns.lean`](../IncComp/NonLocalAns.lean)) | several units (`hashDeps`) | the trace and the unit | `locality`; T5 in [`Classpath.lean`](../IncComp/Classpath.lean) |

Each restates `envOf`, `override`, `round`, `changed`, `invalidated`, `zinc`, `UpToDate`, `Inv`, and reproves T2 and T3a. [`Tree.lean`](../IncComp/Tree.lean) is [`Soundness.lean`](../IncComp/Soundness.lean) with one line changed (REVIEW-2026-10-11, finding 1).

The real cost is that an instance needing two features has nowhere to go. Implicit search needs keys from the output, because the resolved scope is in the output and not the trace's last query. It also needs non-local answers, to live on the shared names instance `SplitProof.Spec` with its `Up`/`S` split. So implicit search sits apart in `GivensSpec.lean`. Phase 14 and the upstream cases will hit the same wall.

## Decision (approved; merged in [talks#37](https://github.com/retronym/talks/issues/37), #46, #47)

**One general structure, [`XCompiler`](../IncComp/General.lean#L20) ([`General.lean`](../IncComp/General.lean)).** It has [`NCompiler`](../IncComp/NonLocalAns.lean#L32)'s fields, except that the extractor also reads the output: `keys : CUnit → Out → List (CUnit × Q) → Finset (CUnit × K)`. `round` records `keys d (out' d) (trace …)`.

The affected units are a decidable predicate, `Affected R s c := c ∈ R ∨ ∃ d ∈ hashDeps c, d ∈ R`, not a `Finset` over `univ`. That way neither the general form nor any variant needs `Fintype CUnit`. `GivensSpec`'s units have none, and `Compiler`'s and [`TCompiler`](../IncComp/Tree.lean#L24)'s theorems never asked for it.

Proved once on [`XCompiler`](../IncComp/General.lean#L20):
- T2 (`round_preserves`) and T3a (`zinc_sound`);
- T4 for monotone policies (`zinc_some_of_monotone`, `zinc_some_of_monotoneFrom`);
- T5 and the snapshot results (`inv_external`, `downstream_sound`, `zinc_out_outside`, `fresh_refreshAll`, `fresh_refreshRef_local`).

The design originally said to change `NCompiler.keys` in place. That would have meant editing the `keys` field and coverage statements of six instances (Erasure, Flat, ImplicitScope, Snapshot, SplitProof, GivensSpec) while instance PRs are open. A new structure that [`NCompiler`](../IncComp/NonLocalAns.lean#L32) lifts into, like the others, leaves every instance untouched.

**Every variant lifts into it.** Each lift is `toX`, with `toX_obligations` and an equality lemma: `invalidated_toX`, plus `zinc_toX` for the loop.

| Variant | Lift | Its theorems, now corollaries |
|---|---|---|
| `Compiler` ([`Soundness.lean`](../IncComp/Soundness.lean)) | hashes local (`hashDeps _ c = {c}`), keys from the trace | `round_preserves`, `zinc_sound`; `Termination`'s monotone regimes |
| [`TCompiler`](../IncComp/Tree.lean#L24) ([`Tree.lean`](../IncComp/Tree.lean)) | hashes local, keys from the output | `round_preserves`, `zinc_sound` |
| [`GCompiler`](../IncComp/NonLocal.lean#L25) ([`NonLocal.lean`](../IncComp/NonLocal.lean)) | answers local, `hashDeps` as given | T2′ `round_preserves`: its `affected` (via `hashRevDeps`, which contains the reverse of `hashDeps`, obligation `rev`) contains the general form's, so its dirty set is larger and its invariant weaker ([`invalidated_toX_subset`](../IncComp/NonLocal.lean#L147)) |
| [`NCompiler`](../IncComp/NonLocalAns.lean#L32) ([`NonLocalAns.lean`](../IncComp/NonLocalAns.lean), [`Classpath.lean`](../IncComp/Classpath.lean)) | keys ignore the output; its definitions coincide with the lift's | T2″, T3a″, T5 and the snapshot results |

**T3b and T3 for [`TCompiler`](../IncComp/Tree.lean#L24) instances** (the coordinator's note 1). A per-unit fixed point and the clean build do not mention keys. So [`TCompiler.toCompiler`](../IncComp/Uniqueness.lean#L165), which forgets the keys, reaches `Uniqueness`'s [`fixpoint_unique_of_wf`](../IncComp/Uniqueness.lean#L64) and `fixpoint_unique_of_explicit` directly. [`cleanFrom_fixpoint_of_comp`](../IncComp/Uniqueness.lean#L43) needs only compositionality. With the [`TCompiler`](../IncComp/Tree.lean#L24)'s own T3a, that gives T3: [`TCompiler.zinc_eq_clean_of_explicit`](../IncComp/Uniqueness.lean#L188) and [`TCompiler.zinc_eq_clean_of_wf`](../IncComp/Uniqueness.lean#L203), a few lines each. T4's monotone regimes reach [`TCompiler`](../IncComp/Tree.lean#L24) through its lift ([`TCompiler.zinc_some_of_monotoneFrom`](../IncComp/Uniqueness.lean#L233)).

Not moved: T4's explicit-interface and acyclic regimes ([`zinc_some_of_explicit`](../IncComp/Termination.lean#L99), [`zinc_some_of_wf`](../IncComp/Termination.lean#L183)). They read the round's recorded keys, and no [`TCompiler`](../IncComp/Tree.lean#L24) instance needs them yet. Moving them is the same pattern when one does.

**`Model.lean` stays the first page.** Its docstring introduces the variants and the general form they lift into. docs/specification.md and the README point there first.

**Step 2** (merged, [talks#46](https://github.com/retronym/talks/issues/46)): implicit search on `SplitProof.Spec`'s scopes as an [`XCompiler`](../IncComp/General.lean#L20) ([`SpecGivens.lean`](../../zinc/Zinc/Features/SpecGivens.lean)). Its search asks the whole level of its hit, its keys read the resolved scope from the output, and `GivensSpec.lean` (the separate [`TCompiler`](../IncComp/Tree.lean#L24) over `Pkg × N`) is gone. Names stay on `Spec`'s [`NCompiler`](../IncComp/NonLocalAns.lean#L32): it already lifts into [`XCompiler`](../IncComp/General.lean#L20), and moving it would change only its declaration, against an open PR's file.

## Rejected

- **A sum type of the four.** Every theorem would case on the variant, and nothing would get simpler.
- **Moving every instance to [`NCompiler`](../IncComp/NonLocalAns.lean#L32) declarations.** It churns files that work, and conflicts with every open instance PR. The lift gives the same results without touching them.
- **Generalising `Compiler` instead.** [`NCompiler`](../IncComp/NonLocalAns.lean#L32) is already the most general in three of the four directions (non-local answers, non-local hash, `locality`), and it is where T5 lives.

## Steps

- [x] 1. [`XCompiler`](../IncComp/General.lean#L20) ([`General.lean`](../IncComp/General.lean)) with T2, T3a, T4 (monotone), T5 and the snapshot results; lifts and corollaries for `Compiler`, [`TCompiler`](../IncComp/Tree.lean#L24), [`GCompiler`](../IncComp/NonLocal.lean#L25) and [`NCompiler`](../IncComp/NonLocalAns.lean#L32); [`TCompiler.toCompiler`](../IncComp/Uniqueness.lean#L165) with T3; [`Policy.InS`](../IncComp/Model.lean#L121) and [`Policy.MonotoneFrom`](../IncComp/Model.lean#L125) moved to `Model.lean`. No instance file changed.
- [x] 2. Implicit search on `Spec`'s scopes as an [`XCompiler`](../IncComp/General.lean#L20) ([`SpecGivens.lean`](../../zinc/Zinc/Features/SpecGivens.lean)): a level-wise search and keys read from the output; `GivensSpec.lean` removed. Names stay on `Spec`'s [`NCompiler`](../IncComp/NonLocalAns.lean#L32), which lifts into [`XCompiler`](../IncComp/General.lean#L20): moving it would only change its declaration.
- [x] [`scripts/Axioms.lean`](../../../scripts/Axioms.lean) checks the axioms of 74 declarations ([talks#36](https://github.com/retronym/talks/issues/36), #37, and later additions): T1; T2, T3a per framework variant and on [`XCompiler`](../IncComp/General.lean#L20); T3b, T3, T4 and T5; the counterexamples that once used `native_decide` ([`PingPong.zinc_diverges`](../../zinc/Zinc/Loop/PingPong.lean#L217), [`Stale.stale_unsound`](../IncComp/Stale.lean#L130), [`stale_affected`](../IncComp/Stale.lean#L135)); a selection of instance soundness theorems and witnesses (`JavaSpec`, `JavaSealedSpec`, `JavaOrder`, `SplitProof.Spec`, `Cycles`, `Annotations`, `HashForms`, `Naming`, `PipelineLifecycle`, `Synthetic`, [`InlineOpaqueSpec.fix_sound`](../../zinc/Zinc/Features/InlineOpaqueSpec.lean#L469), [`InlineOpaqueSound.denot_sound`](../../zinc/Zinc/Features/InlineOpaqueSound.lean#L631), [`MacroDeps.fix_sound`](../../zinc/Zinc/Features/MacroDeps.lean#L385), [`Erasure.dep_sound`](../../zinc/Zinc/Features/Erasure.lean#L1127), [`ImplicitScope.is_sound`](../../zinc/Zinc/Features/ImplicitScope.lean#L574), [`Flat.flat_sound`](../../zinc/Zinc/Bridges/Flat.lean#L760), `Hier.{D,W,Mk}_obligations`, `Sam`); the files layer; B4 and the shared `AsSeenFrom`. `#print axioms` follows dependencies, so each listed theorem also checks the obligations it uses. Not every instance theorem is listed: for example [`DerivedApi.fix_sound`](../../zinc/Zinc/Features/DerivedApi.lean#L222), [`Extensions.ext_rule_obligations`](../../zinc/Zinc/Features/Extensions.lean#L76), [`ExtraHash.qualified_sound`](../../zinc/Zinc/Bridges/ExtraHash.lean#L50), [`SplitProof.proposed_sound`](../../zinc/Zinc/Features/SplitProof.lean#L194), `Classpath` and `Snapshot` are not.
- [x] 3. T5a needs only the abstraction obligation ([`XCompiler.Abstraction`](../IncComp/General.lean#L56)), and [`TCompiler.downstream_sound`](../IncComp/Uniqueness.lean#L220) is a corollary through the lift ([talks#47](https://github.com/retronym/talks/issues/47)). Both are from the split-layout session's `External.lean` ([talks#45](https://github.com/retronym/talks/issues/45)), which was closed as redundant: a `View` structure would have been a fifth copy of `Inv`, `Fresh` and the external invalidation.
