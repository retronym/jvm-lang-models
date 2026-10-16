# The Zinc slice: using the model to decide and to build the Merkle PoC

16 October 2026. A companion to [`2026-10-16-refined-plan.md`](2026-10-16-refined-plan.md), cut to one question: the Merkle hashing proof of concept in retronym/zinc (`integration/merkle`, built from [rz#24](https://github.com/retronym/zinc/issues/24) and [rz#30](https://github.com/retronym/zinc/issues/30) with [rz#29](https://github.com/retronym/zinc/issues/29)'s bridge-side hashing, [rz#48](https://github.com/retronym/zinc/issues/48)'s 1.x backport and the Scala 3 branches on retronym/scala3) has a list of design decisions, open holes and assumptions. For each, what does the model say today, what would it take for the model to decide it, and what does Zinc do with the answer. The point is to make the model the place where a PoC decision is *settled* before Zinc code is written, and the place a PR description points to when it says why a rule is there.

Sources: `PLAN-merkle-poc.md`, `MERKLE-SPARK-CROSSMODULE.md` and `DescendantRules.scala` on the integration branch; [`Flat.lean`](../../../packages/zinc/Zinc/Bridges/Flat.lean), [`FlatRules.lean`](../../../packages/zinc/Zinc/Bridges/FlatRules.lean), [`Stale.lean`](../../../packages/inc-comp/IncComp/Stale.lean), [`HashForms.lean`](../../../packages/zinc/Zinc/Bridges/HashForms.lean), [`ExtraHash.lean`](../../../packages/zinc/Zinc/Bridges/ExtraHash.lean), [`MacroDeps.lean`](../../../packages/zinc/Zinc/Features/MacroDeps.lean), [`InlineOpaqueSpec.lean`](../../../packages/zinc/Zinc/Features/InlineOpaqueSpec.lean), [`ZincBridgeLibs.lean`](../../../packages/links/Links/ZincBridgeLibs.lean) and the phase index [`packages/zinc/docs/README.md`](../../../packages/zinc/docs/README.md).

## 1. What the model has already decided for the PoC

Three things, each of which changed Zinc code, which is the standard the rest of this document holds itself to.

- **Freshness over the descendant closure** (PoC decision 2). [`Stale.stale_unsound`](../../../packages/inc-comp/IncComp/Stale.lean#L132): a non-local hash diffed over the recompiled set alone undercompiles; over `affected` it does not. The PoC diffs over `recompiled ∪ inheritance.reverse*(recompiled)` and follows all four edge kinds over the closure because of it.
- **The `abstract` rule counts names deferred in any ancestor**, not only the changed class: 672 unclean runs of the exhaustive space otherwise (`FlatRules`), and the scripted test `merkle-abstract-ancestor`.
- **Flattened composition over a stored linearization is sound only if a header change recompiles every transitive descendant** ([`Flat.flat_sound`](../../../packages/zinc/Zinc/Bridges/Flat.lean#L843)), so `header` went back into `default`.

Two more were found by the PoC and are now *explained* by the model after the fact, which is weaker but still useful: the trait `extraHash` folding in class parents ([`ExtraHash`](../../../packages/zinc/Zinc/Bridges/ExtraHash.lean), [sbt/zinc#1794](https://github.com/sbt/zinc/issues/1794)'s shape) and companion conflation ([`Companions`](../../../packages/zinc/Zinc/Bridges/Companions.lean), the harness agreeing with the model on all 135 edits before and after [rz#56](https://github.com/retronym/zinc/issues/56)).

## 2. The decision ledger

Each row is a PoC decision, hole or assumption. "Model today" is what exists in the tree; "to decide" is the smallest model change that settles it; "Zinc action" is what follows. Rows are ordered by how much Zinc work waits on them.

### 2.1 Precision: which rules buy what

*Status (16 October, later):* done as phase 30, [`packages/zinc/docs/30-precision.md`](../../../packages/zinc/docs/30-precision.md): the definition and theorems in [`General.lean`](../../../packages/inc-comp/IncComp/General.lean), the preset table from `lake exe exhaustive precision`.

**The PoC's claim is precision, and the model has no definition of it.** The rule table went from eight to six by ablation on scripted tests; `traitDirect` was narrowed after the Spark cross-module run; "narrower `conflicts`" and "`trait` only for concrete members" sit in future work; `traitDirect` still fires on core-internal traits. Each of these is a question of the form "on which edits does rule set A recompile a unit that rule set B does not, and is B still clean", and `FlatRules` can answer it exactly: [`FlatRules.unclean`](../../../packages/zinc/Zinc/Bridges/FlatRules.lean) already decides cleanliness per rule set over 216,000 configurations, and the recompiled set per run is computed on the way.

*Model today:* soundness per preset by kernel `decide`; minimal counterexamples per ablated rule; no over-invalidation count. *To decide:* `overInvalidated` on [`XCompiler`](../../../packages/inc-comp/IncComp/General.lean#L22) (units whose keys changed minus units whose traced answers changed, the definition [`docs/specification.md`](../../specification.md) states in prose), the inclusion theorem (a policy that fires on a subset of edits over-invalidates no more), and a per-preset count over `FlatRules` for `all`, `strict`, `default`, `default` with the narrowed `conflicts` and `trait`, and `none`. One session. *Zinc action:* the preset the numbers pick becomes `default`; each narrowing ships with its minimal counterexample from the ablation as the scripted test, as `merkle-abstract-ancestor` did; the PR description carries the table. This also answers the open "`traitDirect` on core-internal traits" and the `Expression` edit/revert asymmetry (28 against 35 classes): both are over-invalidation with a cause the model can name.

### 2.2 Rule-table parity between Zinc and the model

*Status (16 October, later):* one gap found and closed the other way round: the model's `traitDirect` lacked Zinc's class-or-object clause (retronym/zinc e1bf9d747), so it was the conservative rendering; aligned in phase 30, with a scripted test added on the Zinc side. `annotated`, `exports` and the downstream `traitDirect` composition are still not in `FlatRules`.

The model's rule inductive is `uses`, `overrides`, `conflicts`, `abstract`, `header`, `trait`, `traitDirect`, `mirror` (and `traitPub` as an ablation). Zinc's `default` now also has `annotated` (test discovery reads inherited annotations) and `exports` (a wildcard `export` is recorded as inheritance), and `traitDirect`'s downstream fix composes a trait's API from its trait ancestors only, under names no client uses. None of the three is in `FlatRules`, so the exhaustive check no longer checks the preset Zinc ships.

*To decide:* add the three rules to [`FlatRules`](../../../packages/zinc/Zinc/Bridges/FlatRules.lean), with the observables they need (an annotation flag on a member, an `export` clause as a parent kind, a trait ancestor's own-name contributions), and re-run the ablation. [`Annotations.lean`](../../../packages/zinc/Zinc/Features/Annotations.lean) and [`DerivedApi.lean`](../../../packages/zinc/Zinc/Features/DerivedApi.lean) already have the queries. One to two sessions. *Zinc action:* any new minimal counterexample is a scripted test; the ablation list in the PoC plan is regenerated from the model rather than maintained by hand.

### 2.3 "A descendant is a memberRef client of its parent"

The PoC dropped `uses` and `fallbacks` because every descendant is recorded as a `memberRef` client of its direct parent (constructor call, inherited selections), and keeps `header` only as defence in depth. The model has this as the policy invariant `memberRef ⊇ inheritance`, named in the bug map (K-L1) because [sbt/zinc#1528](https://github.com/sbt/zinc/issues/1528) broke it for local classes. It is an assumption of [`flat_sound`](../../../packages/zinc/Zinc/Bridges/Flat.lean#L843)'s application to Zinc, and it is a property of the real bridge, not of the model.

*To decide:* state it as an explicit hypothesis of the theorem that applies [`flat_sound`](../../../packages/zinc/Zinc/Bridges/Flat.lean#L843) to the PoC's `Δ` domain (`FlatRules` checks the PoC's literal domain already), and enumerate in the model the shapes where a descendant selects nothing from its parent (an empty class extending a trait with no constructor call recorded, a Java parent, a local class). *Zinc action:* an assertion at analysis time that every internal inheritance edge has a matching `memberRef` edge, logged when it fails, run over the scripted suite and catalyst. If it never fires, `header` can be argued redundant with evidence; if it does, the shape is a scripted test. Half a session each side.

### 2.4 Libraries as coarse ancestors

Assumption 6 of the PoC: folding jar stamps into inherited-name hashes is sound under `libraryAncestors=names` and unsound under `stubs-only` (`merkle-libjar-override`). Option 2 replaces stamps by per-name hashes of the library's classes, cached per jar version.

*Model today:* [`ZincBridgeLibs.stamp_covers`](../../../packages/links/Links/ZincBridgeLibs.lean#L63): a library unit's stamp key covers every query on it, and [`library_client`](../../../packages/links/Links/ZincBridgeLibs.lean#L107) is T5a plus [`untouched_eq_clean`](../../../packages/inc-comp/IncComp/General.lean#L578). That is the soundness of `names` for *clients*; the PoC's step is folding the stamp into the *descendant's* inherited names, which is a non-local hash with `hashDeps` reaching the jar. *To decide:* the `names` design as a key on the descendant whose hash reads the jar stamp, proved to meet the obligations, and `stubs-only` as a coverage failure with `merkle-libjar-override`'s shape as the witness; then option 2 as a per-name key whose hash is the library class's own name hash, which is local to the jar version and so needs no freshness walk (the `Stale` remark about hashes stored at the owner). One session. *Zinc action:* option 2's design note cites the theorem; the "known coarseness" (every inherited name moves on any jar change, platform names included) is quantified by the precision count of §2.1 on a space with a library ancestor.

### 2.5 Bridge-side hashing: what the equivalence check must compare

H2 computes name hashes from compiler types without building the `xsbti.api` tree, and `CHECK` mode asserts equality-only agreement with the tree path (0 disagreements on 34,000 classes). The model's statement of what must hold is [`HashForms`](../../../packages/zinc/Zinc/Bridges/HashForms.lean) (phase 17): `π` must be a function of the interface across the forms the next run compares (source in the round, pickle otherwise), with [`abstraction_formed_iff`](../../../packages/zinc/Zinc/Bridges/HashForms.lean#L54) and [`canonical_stable`](../../../packages/zinc/Zinc/Bridges/HashForms.lean#L74). The H2 risk list says exactly this ("hash stability between typing from source and unpickling must be preserved") and the Scala 3 determinism findings ([scala/scala3#26551](https://github.com/scala/scala3/issues/26551), [retronym/scala3#3](https://github.com/retronym/scala3/issues/3) and #10) are its failures.

*To decide:* nothing new in Lean; the model already names the two views. *Zinc action:* `CHECK` mode today compares bridge against tree within one form. Add the cross-form comparison the theorem asks for: hash each class once from source and once from its own pickle in a following run, and report disagreements. On Scala 3 this is the determinism suite; on Scala 2 it has not been run, and the name-hash contract's special cases (`sbt/sbt#1079`'s refinement-relative names, existential renaming) exist because earlier versions of this comparison failed. The [scala/scala3#27271](https://github.com/scala/scala3/issues/27271) bug (`apiModifiers` with a type-only `FlagSet`, so deferred terms were never abstract) is an abstraction failure of `π` that a model instance whose `π` *is* the contract would have exhibited; see §3.

### 2.6 The macro contract

Decision of 9 October: macros that observe more than the public API are outside Zinc's contract. The model's [`MacroDeps.private_today`](../../../packages/zinc/Zinc/Features/MacroDeps.lean) is the witness (an abstraction failure under today's `api` key), and [`bytecode_coarse`](../../../packages/zinc/Zinc/Features/MacroDeps.lean#L488) and [`private_coarse`](../../../packages/zinc/Zinc/Features/MacroDeps.lean#L496) cost the two alternatives the PoC considered.

*To decide:* decided; what is missing is the record. *Zinc action:* the contract line in the PoC plan should cite the witness as the named exclusion, as `bug13199` is named in `Refchecks`, and the pending test `macro-observes-private-member` stays pending with that citation. If the decision is revisited, the model's two costs are the comparison.

### 2.7 Inline soundness on Scala 3

The PoC plan lists three suspected holes in stock Zinc: `treeHash` covers tree shape and names but not symbols or types; an expansion records no dependencies (`summonInline`, `compiletime` matches); a macro implementation in another class is not part of the macro's API. The model has I1 to I3 and O1 in [`InlineOpaqueSpec`](../../../packages/zinc/Zinc/Features/InlineOpaqueSpec.lean) and the macro edges in `MacroDeps`, but not these three.

*To decide:* three witnesses: the first is an abstraction failure (two bodies with equal `treeHash` and different resolved overloads), the second and third coverage failures (a query the expansion asks that no key covers). Each witness prints the minimal program. One session. *Zinc action:* the three programs become scripted probes under stock Zinc first, as the plan says; the fix for each is the key the witness names (hash the resolved symbol into `treeHash`; record the expansion's lookups as the client's; a macro's implementation class in its API hash).

### 2.8 The `ExternalLookup` fast track

Known gap: sbt's own hook bypasses `MerkleHashes`. In the model's terms this is [`stale_unsound`](../../../packages/inc-comp/IncComp/Stale.lean#L132) by construction: a client whose composed hash is never recomputed. *To decide:* nothing; the theorem is the argument. *Zinc action:* a scripted test with a cross-project ancestor edit through the fast-track path, expected to fail until the hook composes.

### 2.9 Header detection and `bytecodeHash`

Known gap: header changes are detected through `bytecodeHash` when `HashAPI` misses them. [`flat_sound`](../../../packages/zinc/Zinc/Bridges/Flat.lean#L843) makes the header rule load-bearing, so a header change `HashAPI` misses and `bytecodeHash` also misses is an unsoundness. The pre-existing `final`-parent undercompile (`HashAPI.hashAPI` skipping a top-level class's own modifiers) was one. *To decide:* enumerate the header fields the model's `(p, parents)` key hashes (parents, kind, finality, type parameters, self type, access, modifiers, annotations) against what `AncestorChange.header` hashes in `DescendantRules.scala`; any field in the first list and not the second is a candidate witness. Half a session, and it is a reading exercise more than a proof. *Zinc action:* close the list, and drop the `bytecodeHash` fallback once the header hash is complete, since the fallback is what makes pipelined builds (no bytecode) a different case.

### 2.10 Per-compile overhead

The cross-module run shows about 0.3 s extra on a body-only edit, attributed to `Lookup` composing hashes for every upstream class without memoisation. The model says nothing about cost and should not; measure it. The only model input is which composed hashes a round *needs*: those of the hash dependents of the recompiled set, which `Stale` already defines, so a memo keyed by that set is the right shape.

## 3. The instance that is Zinc

Every row above becomes cheaper once one thing exists: an [`XCompiler`](../../../packages/inc-comp/IncComp/General.lean#L22) instance whose `π` is the name-hash contract H2 wrote down (the per-name hash over the `UseScope` partition, salted by class name and namespace; `extraHash` with trait breakers; `apiHash` over linearized parents as seen from the class) and whose `keys` are what `ExtractUsedNames` and `Dependency` record (memberRef on the owner, inheritance, local inheritance, macro expansion, used names by scope). Today every instance is a toy with Zinc-shaped keys; none is Zinc. With this instance:

- the rule table (§2.1, §2.2) is one `Policy` on one instance, compared with `all` by the precision theorem rather than on a toy's `Rule` inductive;
- the H2 equivalence check (§2.5) has a statement: bridge `π` equals contract `π` on equality, and `HashForms` says across which forms;
- [scala/scala3#27271](https://github.com/scala/scala3/issues/27271)-shaped bugs (a modifier the contract hashes and the bridge drops) are abstraction failures of a stated function, exhibitable in the model before a release;
- the lookup-trace tool of the refined plan (§5.4 there) checks this instance's coverage on catalyst, which is the first time coverage would be checked against what the bridge actually records rather than what a toy says it records.

The name-hash contract is the specification; the instance is its model; the bridge is its implementation; `CHECK` mode and the lookup trace are the calibration. That is the same four-part structure the JVM and Scala layers have, applied to Zinc itself, and it is the reason the previous plan's "start with the core" reading points here. Two to three sessions for the instance; it reuses `Flat`'s language and `FlatShared`'s embedding, so the existing spaces run on it unchanged.

## 4. How to run a PoC decision through the model

The loop, so it can be applied without judgement about Lean:

1. **A rule changes.** Add or narrow it in `FlatRules.Rule` first; run `lake exe exhaustive`; the result is either "clean on the space, over-invalidation N" or a minimal counterexample. The counterexample is the scripted test; the number goes in the PR. Then write the Zinc code.
2. **A hash or key changes.** State the new `π` or `keys` on the instance; prove or refute abstraction and coverage for the instance's queries. A refutation names the program; `CHECK` mode or a scripted test confirms it on real Zinc. Then write the bridge code.
3. **A policy or walk changes** (what is diffed, over which set, in which round). Check it against `Stale`, `Cycles` and `Files`: these are the three places Zinc's loop has been shown to differ from the clean build, and each has a theorem whose hypothesis the change either keeps or breaks.
4. **A scope decision** (something declared outside the contract). Name the witness in the model as an exclusion, and cite it where the decision is recorded.
5. **Every PoC PR** names the Lean declaration that justifies its soundness claim and the space its precision number comes from, as [`flat_sound`](../../../packages/zinc/Zinc/Bridges/Flat.lean#L843) and the 672 are cited today. Where no declaration exists, that is the model work to do first, not a footnote.

What the model does not do, and should not be asked to: completeness of the rule table against scalac (`mirror` and `trait` came from thinking about bytecode; specialization, `-opt:inline`, value classes over universal traits and Scala 3 trait parameters are unprobed), per-compile cost, and the batch nondeterminism of the compilers. Those are the conformance harness, the profiler and the determinism suite, and the PoC plan's step 4b (a generator of random hierarchies and edits compared against a clean build) is still the cheapest way to widen the first. The `FlatRules` space rendered as Scala through `FlatShared` is such a generator already, with 48,000 distinct programs; running it through the conformance harness on `integration/merkle` under `default`, `strict` and `none` is the ablation at scale on real Zinc, and has not been done.

## 5. Order

1. §2.1 precision definition and the preset table on `FlatRules`; §2.2 rule parity. Together one to two sessions, and they settle the open rule questions in the PoC plan before any more Zinc code.
2. §2.9 header-field audit and §2.3 the invariant assertion: two half-sessions of reading and a logging change, with a chance of a real undercompile each.
3. §2.7 inline witnesses, then the scripted probes on stock Zinc: the likeliest new upstream bugs in this slice.
4. §3 the Zinc instance, then the lookup trace against it on catalyst.
5. §2.4 library ancestors and §2.5 cross-form `CHECK`, when option 2 or the Scala 2 determinism question comes up.
6. §2.6, §2.8, §2.10 are bookkeeping, a test and a measurement.
