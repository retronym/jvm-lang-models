# `Zinc`

Zinc as instances of `IncComp`: its loop and policies (`Zinc.Loop`), its bridges and their variants (`Zinc.Bridges`: Scala 2's as-seen-from members, Scala 3's as-declared ones, the Merkle PoC, hash forms, naming, companions), and each Scala and Java feature (`Zinc.Features`). For each: the compiler's algorithm as the task, today's bridge as keys, each bug family as a failed obligation with a witness, each fix as keys with the obligations proved.

**Start here.** [`Zinc/Features/Sam.lean`](Zinc/Features/Sam.lean) is the template for a feature; [`docs/28-sam.md`](docs/28-sam.md) the question behind it. [`docs/evidence/bug-map.md`](../../docs/evidence/bug-map.md) (repository root) maps 145 Zinc and compiler bugs to these files.

**Calibration.** The conformance harness ([retronym/zinc#25](https://github.com/retronym/zinc/issues/25), #36) runs these spaces through real Zinc and compares classfiles with a clean build; on the names and givens spaces the model and Zinc agree on every verdict and recompiled set (2,331 + 2,372 cases). 20 failures the model predicted all failed on Zinc `develop`.

**Gaps.** `Hier`, `Erasure`, `Flat` and `ImplicitScope` each carry their own toy Scala instead of `scala-types`; see [`docs/roadmap.md`](../../docs/roadmap.md) at the repository root.

## Files

| File | Contents |
|---|---|
| [`Files.lean`](Zinc/Loop/Files.lean) | Files as a layer: file-closed policies, imports charged to one class of a file; `zinc_sound_charged`, T5 under charging (`downstream_sound_charged`), the [sbt/zinc#417](https://github.com/sbt/zinc/issues/417) fix for every program (`Fi.kept_sound`) |
| [`Naming.lean`](Zinc/Bridges/Naming.lean) | Class-name agreement between what the compiler reads and what the bridge records; `spelling_bugs`, case-insensitive collisions |
| [`HashForms.lean`](Zinc/Bridges/HashForms.lean) | Hash stability across forms (tree, pickle, TASTy, classfile): abstraction holds iff no form masks a difference; canonical forms |
| [`Hier.lean`](Zinc/Bridges/Hier.lean), [`HierSound.lean`](Zinc/Bridges/HierSound.lean) | Toy class hierarchy; designs `D` (decls + walk), `W` (materialised members), `Mk` (Merkle) all meet their obligations |
| [`Flat.lean`](Zinc/Bridges/Flat.lean) | The Merkle PoC's flattened hash over a stored linearization: `Fl_obligations`, `flat_sound`; header and refchecks keys and their ablation |
| [`Erasure.lean`](Zinc/Features/Erasure.lean) | Erasure through inheritance (as seen from vs as declared; value classes, intersections): witnesses, a dependency edge, `dep_sound`; `lake exe exhaustive erasure` |
| [`ImplicitScope.lean`](Zinc/Features/ImplicitScope.lean) | Implicit scope through an ancestor's companion across projects ([sbt/zinc#1845](https://github.com/sbt/zinc/issues/1845)): `is_obligations`, `is_sound`, `stored_eq_recomputed`; `lake exe exhaustive implicit` |
| [`SplitProof.lean`](Zinc/Features/SplitProof.lean) | The shared names instance `Spec` (a slot language, units split upstream and downstream): today's and #34's failures, the rules' obligations, precision, F4/F5 as `joint_not_comp`, `cross_downstream_sound` |
| [`SpecGivens.lean`](Zinc/Features/SpecGivens.lean) | Implicit search on `Spec`'s scopes, as an `XCompiler`: G1/G2 (`g12_today`), the G rule's obligations, #24's `g_decls_not_abstraction` |
| [`Extensions.lean`](Zinc/Features/Extensions.lean) | Member selection through extensions (Scala 3 `extension`, Scala 2 implicit classes) on `SpecGivens`' search: `ext_rule_obligations`, today's failures |
| [`Added.lean`](Zinc/Features/Added.lean), [`Sealed.lean`](Zinc/Features/Sealed.lean) | Added and deleted classes as absent sources (F1); sealed children in the hash, Java `permits` |
| [`Inline.lean`](Zinc/Features/Inline.lean) | Bodies as API (Scala 3 `inline`, Scala 2 `@inline`, Java constants) with pipelining: `obligations_withBodies`, `pipelined_ne_final` |
| [`PipelineLifecycle.lean`](Zinc/Loop/PipelineLifecycle.lean) | Pipelining's early output: `rollback_preserves` with [sbt/zinc#1843](https://github.com/sbt/zinc/issues/1843); `noRollback_breaks`, `stale_after_revert` without it |
| [`InlineOpaqueSpec.lean`](Zinc/Features/InlineOpaqueSpec.lean) | Scala 3 `inline` and opaque types as a `TCompiler`: I1–I3 and O1 witnesses, `fix_sound`, precision per key |
| [`InlineOpaqueSound.lean`](Zinc/Features/InlineOpaqueSound.lean) | The same observables as an `NCompiler`: the denotation hash's `denot_sound`, `I1_abstraction` |
| [`MacroDeps.lean`](Zinc/Features/MacroDeps.lean) | Scala 3 macro dependencies: a witness per bug, `fix_sound`, costs; `private_today`, a prediction not yet run |
| [`Annotations.lean`](Zinc/Features/Annotations.lean) | Annotations as API and as dependencies: [sbt/zinc#1842](https://github.com/sbt/zinc/issues/1842)'s fix (`fix_sound`), `today_not_coverage`, [scala/scala3#22999](https://github.com/scala/scala3/issues/22999) |
| [`DerivedApi.lean`](Zinc/Features/DerivedApi.lean) | Export forwarders and used types' supertypes: `fix_sound`, `export_not_coverage`, `usedType_not_coverage` |
| [`Synthetic.lean`](Zinc/Features/Synthetic.lean) | Constructors and synthetic case-class members: manglings that agree are sound, ones that disagree under- or over-invalidate |
| [`ExtraHash.lean`](Zinc/Bridges/ExtraHash.lean) | Companion pairs under one name: merged keys are spurious, per-namespace keys precise and sound; private members of ancestors |
| [`JavaSpec.lean`](Zinc/Features/JavaSpec.lean), [`JavaSealedSpec.lean`](Zinc/Features/JavaSealedSpec.lean) | Java name resolution (JLS 6.4.1, 7.5) and sealed exhaustivity as `TCompiler`s: J1–J4, S1, S2, `fix_sound` |
| [`JavaOrder.lean`](Zinc/Features/JavaOrder.lean) | A Java class's source and classfile views: `mixed_sound` under view agreement, `early_view`, `exclusion_exact`, `flip_spurious` ([sbt/zinc#1819](https://github.com/sbt/zinc/issues/1819)) |
| [`Sam.lean`](Zinc/Features/Sam.lean) | SAM conversion and local classes: P1/P2 witnesses, `fix_sound` (Phase 28, [retronym/zinc#58](https://github.com/retronym/zinc/issues/58)) |
| [`Toy.lean`](Zinc/Toy.lean), [`Examples.lean`](Zinc/Examples.lean) | A toy language for §15a (implicits) and §15b (value classes); name-only vs repaired keys, `repaired_sound`, `repaired_terminates` |
| [`TreeToy.lean`](Zinc/Features/TreeToy.lean) | `+=` desugaring and pattern-matcher selectors: Zinc's tree extractor fails coverage; failed lookups and an arity sentinel fix it |
| [`Snapshot.lean`](Zinc/Loop/Snapshot.lean) | Zinc's snapshot refresh with a non-local hash: edit then revert leaves the downstream stale (`stale_after_revert`) |
| [`PingPong.lean`](Zinc/Loop/PingPong.lean) | `zinc_diverges` without `transitiveStep`; `transitiveStep_stops`; `lake exe exhaustive pingpong` |
| [`Cycles.lean`](Zinc/Loop/Cycles.lean) | Inferred types in a cycle: `zinc_ne_clean`, `two_fixpoints`, `annotated_eq_clean`; [sbt/zinc#1284](https://github.com/sbt/zinc/issues/1284)'s and #1780's rules |
| [`ZincNames/Names.lean`](ZincNames/Names.lean), [`ZincNames/Givens.lean`](ZincNames/Givens.lean) | Name resolution over nine binding scopes, and instances found by type (implicits, givens), per Scala version, with Zinc's recorded edges; a precompiled library, so the checks run natively |
| [`Zinc/Features/NamesRules.lean`](Zinc/Features/NamesRules.lean) | The whole-space checks of the names and givens spaces, per rule and mode |
| [`Zinc/Features/Split.lean`](Zinc/Features/Split.lean) | The names spaces split across subprojects; checks `SplitProof`'s slot language against `Names` |
| [`Zinc/Features/InlineOpaque.lean`](Zinc/Features/InlineOpaque.lean) | Scala 3 `inline` and opaque types as a small key loop, with what dotc 3.9.0 records |
| [`Zinc/Features/JavaNames.lean`](Zinc/Features/JavaNames.lean), [`Zinc/Features/JavaSealed.lean`](Zinc/Features/JavaSealed.lean) | Java name resolution and sealed exhaustivity in mixed builds |
| [`Zinc/Bridges/FlatRules.lean`](Zinc/Bridges/FlatRules.lean) | The Merkle PoC's descendant rules as a policy; `lake exe exhaustive` |
| [`Zinc/Bridges/Companions.lean`](Zinc/Bridges/Companions.lean) | Companion pairs in a hierarchy; the bridge before [retronym/zinc#56](https://github.com/retronym/zinc/issues/56) loses a half (`check_pre56_exact`) |
