# The type of a selected member: one `asSeenFrom` versus a chain of substitutors

A design note for PR [retronym/intellij-scala#5](https://github.com/retronym/intellij-scala/pull/5). It formalizes what scalac computes when it types `pre.m`, what IntelliJ computes instead, under which conditions the two agree, and where IntelliJ's construction cannot be made to agree by local rules alone. It ends with the invariants that would make the chain sound, the restructuring that would make them unnecessary, and how to check either.

## 1. Why this matters

Every false error fixed on this branch has the same shape: a member's type, viewed from the path it was selected through, is spelled differently by IntelliJ than by scalac, and a later comparison (override checking, conformance, equivalence) then fails. The branch fixed these one mechanism at a time (merged base types, anchoring, no self-embedding, owner-chain matching, canonicalization), each one checked against scalac. The remaining failures (`Importers.scala`, `MatchWarnings.scala`, refinement members, sibling-trait spellings) are not isolated bugs. They are consequences of how IntelliJ composes the computation, and the question for the review is whether that composition can be made correct in principle, or whether it is a heuristic that will keep needing a new allowance for each new cake.

## 2. The objects

A **class** `C` has an **owner chain** `C, owner(C), owner(owner(C)), …` ending at a package. For a member `m`, `owner(m)` is the class whose template declares it.

A **type** is built from these leaves, among others:

- `C.this`: the this-type of class `C`. In a declared member type it always means "the instance of `C` that encloses this declaration".
- `p.m`, a projection: member `m` selected from a stable path or prefix type `p`.
- `T#m`, `C[A…]`, compounds, existentials, type parameters: structure that the maps below walk through but do not rewrite.

A **prefix** `pre` is the type of the qualifier of a selection: a this-type, a singleton path `x.y.z.type`, a class type, or a compound.

`baseType(pre, C)` is the instance of class `C` among `pre`'s base types, with the arguments and prefix `pre` sees it with, or none when `C` is not a base class of `pre`. Its prefix, `prefix(baseType(pre, C))`, is "the enclosing instance of `C` as `pre` sees it".

The question is: given a member `m` declared with type `info(m)` inside `owner(m)`, and a prefix `pre` through which `m` is selected, what is the type of `pre.m`?

## 3. scalac: one map, one anchor

`pre.memberType(m) = info(m).asSeenFrom(pre, owner(m))` (`Types.scala`, `computeMemberType`; for methods `typeAsMemberOf` caches the same thing).

`asSeenFrom(pre, clazz)` is `AsSeenFromMap(pre, clazz)` (`TypeMaps.scala`). On a this-type leaf `D.this` it runs `thisTypeAsSeen`, which is the whole semantics:

```
loop(pre, clazz):
  if pre is NoType/NoPrefix or clazz is a package  →  leave D.this alone
  else if clazz == D and baseType(pre, clazz) exists   (matchesPrefixAndClass)
       →  pre   (or an existential capture of pre if pre is unstable)
  else →  loop(prefix(baseType(pre, clazz)), owner(clazz))
start: loop(pre, clazz)
```

Three properties matter for everything below.

**(P1) The cursor is anchored.** The walk starts at `clazz`, the class whose view the type is currently in. The type `info(m)` is written in the view of `owner(m)`, so `memberType` starts there. `D.this` is rewritten only when the cursor *is* `D` (`clazz == candidate` in `matchesPrefixAndClass`); inheritance between `D` and the cursor is checked only through `baseType(pre, clazz)`, never through "is the cursor a subclass of D".

**(P2) Both sides step in lockstep.** When the cursor doesn't match, the walk moves the cursor one step out (`owner(clazz)`) *and* moves `pre` to the prefix of its `clazz`-base-type at the same time. So after k steps, `pre_k` is "the k-th enclosing instance of the original prefix, as the original prefix sees it", and `clazz_k` is the k-th enclosing class of the anchor. The two are always views of the same nesting level.

**(P3) The output only ever strips.** The result for a this-type is some `pre_k`, which is a prefix of a prefix of … of the original `pre`. The map never builds a path that contains the this-type it is replacing, so no result ever needs to be re-run through the same map, and nothing can grow.

Type parameters of enclosing classes go through the same walk (`classParameterAsSeen`), reading arguments off `baseType(pre_k, clazz_k)`; singleton paths `q.x` are mapped by mapping `q`. Everything else is `mapOver`.

`asSeenFrom` is applied to exactly one thing per selection: `info(m)`. The types of the qualifier, the enclosing expression, the match scrutinee and so on are already in the view of the use site and are not mapped again.

## 4. IntelliJ: a chain of links, each with its own anchor

IntelliJ has no single `memberType`. The type of a resolved member is `subst(declaredType(m))`, where `subst` is an `ScSubstitutor`: an array of `Update`s applied as one fused recursive pass (`ScSubstitutor.recursiveUpdateImpl`). When a link replaces a node, the *remaining* links run on the replacement. The chain for a member of a class `C` selected from `pre` is typically

```
subst  =  sig_C(m)  >>  ThisTypeSubstitution(target = pre, seenFromClass = anchor)  >>  …
```

where

- `sig_C(m)` is the **signature substitutor** from `MixinNodes.SuperTypesData(C)`: for each super class `S` in `C`'s linearization, `combine(typeArgs) >> ThisTypeSubstitution(C.this, seenFromClass = S) >> dependentSubst`. It puts a member declared in `S` into `C`'s view: `S.this` becomes `C.this` and `S`'s type parameters become `C`'s arguments for them. This is a cached `asSeenFrom(C.this, S)`, which is exactly what scalac would compute for `C.this.memberType(m)` with `owner(m) = S`.
- the `ThisTypeSubstitution(pre, anchor)` link comes from `ScalaResolveState.substitutorWithThisType(anchor)` in the processors, with `anchor = ScSubstitutor.declarationAnchor(m) = owner(m)`, or from `BaseProcessor.processType` for a value projection, or from `ScProjectionType.actualImpl`, or from `SuperTypesData` itself.
- the tail `…` holds whatever the resolution route accumulated: the qualifier's own substitutor, an export's substitutor, a `matchClauseSubstitutor` from `PatternTypeInference` (type-parameter and this-type narrowing deduced from the pattern), extension-method substitutors.

Each `ThisTypeSubstitution` link is `doUpdateThisTypeFromClass`, a reimplementation of `thisTypeAsSeen` over `BaseTypes.baseType` plus three departures:

1. `seenFromClass = null` selects an anchorless walk, `doUpdateThisType`, which rewrites `D.this` to `target` whenever `target` "is more narrow" than `D` (inherits from it), climbing `target`'s prefixes. This is the pre-branch heuristic and is still reachable (refinement members, synthetic members, `workWithTypeAlias`).
2. An early exit before the walk: if `D` inherits from the cursor and `target` widens to a subclass of `D`, rewrite immediately (scalac's `toPrefix` first branch, needed because IntelliJ's inferred member types can mention a superclass's this).
3. When `baseType(target, cursor)` doesn't exist, instead of stepping to an empty prefix as scalac does, the walk narrows against `target` directly, gated by **owner-chain matching** (`ownerChainMatches`): does the cursor's containing chain reach `D` (same-or-inheritor, and until the WIP commit 36b514d2fb, also through a cursor's self type), or does `target` denote exactly `D`?

And one rule with no scalac analogue: **no self-embedding** (`embedsRewrittenThis`) refuses a result whose spine root is still `D.this` or an inheritor's this. scalac needs no such rule because of (P3); IntelliJ needs it because the result of a link is fed to the rest of the chain and back into resolution, which mints new substitutors from it.

The important structural difference is not any one of these rules. It is that a `ThisTypeSubstitution` link is applied to *whole types in whatever view they happen to be in*, with an anchor chosen by whoever built the link, and composed with other links that have other anchors.

## 5. When is a chain equal to one `asSeenFrom`?

### 5.1 The composition law

Write `A(pre, c)` for `asSeenFrom(·, pre, c)`. The law that scalac relies on, implicitly, is:

> **(L)** If `T` is a type in the view of class `c1`, then `A(p1, c1)(T)` is a type in the view of `pre`'s class, i.e. of `p1`. To view it from somewhere else, the next map must be anchored at the class of `p1`: `A(p2, cls(p1)) ∘ A(p1, c1)  =  A(A(p2, cls(p1))(p1), c1)` when `p1` is a this-type `c1'.this` with `c1' <: c1`, and more generally the composition is the single map from the final prefix when every link's anchor is the class whose view its input is in.

Sketch of why: `A(p1, c1)` sends every `D.this` reachable from `c1`'s owner chain to the corresponding `pre_k` of `p1`. In the result, those leaves are now prefixes of `p1`, so they are in `p1`'s view; the this-types it leaves alone (owner chain exhausted, or an unrelated inner class) are ones scalac would also leave alone from `p1`. Applying `A(p2, cls(p1))` then rewrites `p1`'s own this-leaves and walks `p1`'s prefixes in lockstep with `cls(p1)`'s owner chain, which is exactly what `A(p2', c1)` with `p2' = p1[p2/cls(p1).this]` would do in one pass. The lockstep property (P2) is what makes the two cursors line up.

The law fails whenever a link's anchor is *not* the class whose view its input is in. Two ways to break it:

- **Anchor too early** (anchored at `owner(m)` after `sig_C` has already moved the type into `C`'s view): the walk starts at `owner(m)`, but the this-leaves in the type are now `C.this` and `C`'s outer this-types. `owner(m)` may not be `C` nor on `C`'s owner chain, so the cursor never equals the leaf's class: the rewrite is skipped, and the type keeps a `C.this` it should have lost. Case (b) below.
- **Anchor too late / too coarse** (one link anchored at some class `K` applied to types that are in a *different* class's view, or to types that were never a member info at all): the walk reaches `K`'s owner chain, and any `D.this` for `D` on that chain gets rewritten even though, in the input's actual view, that `D.this` meant something else. Case (a) below.

### 5.2 Links must apply only to member infos

scalac applies `A(pre, owner(m))` to `info(m)` and nothing else. The use site's own types (the scrutinee, the case body's expressions, the qualifier's type) are already in the use site's view and are never passed through a member's map.

In IntelliJ a `matchClauseSubstitutor` built from an extractor pattern `from.TypeRef(...)` carries the substitutor under which the extractor's `unapply` result was viewed (including a `ThisTypeSubstitution(from, owner(unapply))`), and `ScStableCodeReferenceImpl`/`ReferenceExpressionResolver` thread it into the resolve state of *every reference in the case body*. A reference in the body to a member `n` of the enclosing class then gets `subst = sig(n) >> … >> matchClauseSubst`, so `n`'s type is passed through a map anchored at the extractor's owner with target `from`. That map's job was to view `unapply`'s result from `from`; it has no business viewing `n`'s type, which is in the enclosing class's view. This is a leak: a link applied beyond the one type it was built for. It is what rewrote `Importers.this` onto `from` in case (a), and the self-type allowance in owner-chain matching is what let the anchored walk match.

Type-parameter bindings in a match-clause substitutor are a different story: those are substitutions on *names* (type variables narrowed by the pattern), which commute with everything and are safe to apply to whole bodies. The this-type links are the problem, because their meaning depends on the view of their input.

### 5.3 Summary of the conditions

A chain `s_n ∘ … ∘ s_1` applied to `info(m)` equals `A(pre_final, owner(m))(info(m))` when:

1. **Anchor = view.** Each this-type link `s_i = ThisTypeSubstitution(p_i, c_i)` has `c_i` equal to the class whose view the type is in after `s_{i-1} ∘ … ∘ s_1`. For the first this-link that is `owner(m)`; after `sig_C` it is `C`; after a link with target `q.this` it is `q`; after a link with a path target `x.y` it is `cls(x.y)` (the class of the path's widened type), which is the anchor the next link must use.
2. **Links apply only to member infos.** No this-type link reaches a type that was not the declared info (or a view of the declared info) of the member the link was built for.
3. **Each link is a faithful `thisTypeAsSeen`.** The walk matches on `cursor == D`, consults `baseType` for inheritance, and steps both sides in lockstep. No anchorless fallback, no "cursor inherits D" shortcut, no self-type shortcut.
4. **Outputs are not re-run through the same link.** (P3) holds per link, so the fused engine's "rest of chain processes the replacement" is harmless *only* if the later links are correctly anchored per (1). No self-embedding is then unnecessary; while (1) is violated somewhere, it is a necessary brake.

Under these conditions the chain is simply a staged evaluation of one `asSeenFrom`, with the stages being views through successive prefixes, and the composition law makes it equal to the single map. Under any other conditions there is no single `(pre, clazz)` that the chain computes, which is why its results can't be checked against scalac leaf by leaf, only by example.

## 6. The concrete failures, classified

All at scala/scala b4ad4458da.

### (a) `reflect/internal/Importers.scala`: `Importers.this` rewritten onto `from`

```scala
trait Importers { to: SymbolTable =>
  abstract class StandardImporter extends Importer {
    val from: SymbolTable
    def importModifiers(mods: from.Modifiers): Modifiers = …   // Modifiers is Importers.this.Modifiers
  }
}
```

Two routes produced `from.Modifiers`:

- `BaseProcessor.processType` on a value projection `pre.v` built `ScSubstitutor(pre.v, declarationAnchor(v))` and applied it to *all* members of `pre.v`'s type. The anchor is `owner(v)`, the class that declares the `val`; the types being mapped are the member infos of `v`'s *type's* class, in *their* owners' views. Condition 1 violated (anchor = owner of the wrong symbol). With `v = from: SymbolTable`, `owner(from) = StandardImporter`, whose owner chain is `StandardImporter → Importers → …`, so the walk anchored there matches `Importers.this` and sends it to `from`. scalac anchors at `owner(m)` for each `m` of `SymbolTable`, whose chain never passes `Importers` for `Importers.this` as seen from `to`'s own instance. Fixed in WIP 36b514d2fb by passing `pre.v` as `fromType` so each member is anchored at its own owner.
- The self-type allowance in `ownerChainReaches` plus the match-clause leak (§5.2): a `from.TypeRef(...)` pattern's substitutor is applied to case-body references. Condition 2 violated (link applied beyond its member info) and condition 3 violated (self-type shortcut). Removing the allowance fixes the symptom; the leak remains and will reappear with a different shortcut.

**Verdict:** fixable within the chain, and the fix is precisely restoring conditions 1 and 3. The leak (condition 2) is a separate structural problem that the fix only hides.

### (b) `patmat/MatchWarnings.scala`: a link anchored before the signature substitutor moved the view

```scala
trait MatchTranslation { self: PatternMatching =>
  trait MatchTranslator extends TreeMakers with TreeMakerWarnings { … }      // typer: Typer via MatchMonadInterface
}
trait MatchWarnings { self: PatternMatching =>
  trait TreeMakerWarnings { self: MatchTranslator =>
    import typer.context   // typer declared in MatchMonadInterface, used through the self type
  }
}
```

Resolving `typer` on `TreeMakerWarnings.this` goes through its self type `MatchTranslator`, and `BaseProcessor` processes the self type with `ScSubstitutor(TreeMakerWarnings.this, seenFromClass = TreeMakerWarnings)` in the state. The member comes with `sig_MatchTranslator(typer)`, which has already rewritten `MatchMonadInterface.this` into `MatchTranslator`'s view: `MatchTranslation.this.…`. The next this-link is anchored at `TreeMakerWarnings` (the WIP diff) or, in the processors, at `declarationAnchor(typer) = MatchMonadInterface`. Neither is `MatchTranslator`, the class whose view the type is now in, so the lockstep walk starts from the wrong nesting level and never reaches `MatchTranslation.this`. Condition 1 violated (anchor too early). The self-type allowance used to paper over this: `MatchWarnings`' self type `PatternMatching` inherits `MatchTranslation`, so the shortcut "matched".

The WIP in `tckscan-3` anchors the self-type route at `selfType.extractClass` (= `MatchTranslator`), which is condition 1 applied to that one route. But the same shape, "a signature substitutor from `C` followed by a link anchored at `owner(m)` instead of `C`", exists at *every* site that calls `substitutorWithThisType(declarationAnchor(m))` after `MixinNodes` supplied `sig_C(m)`. It works today when `owner(m)` and `C` happen to share the relevant part of the owner chain (most non-cake code) and fails when they don't.

**Verdict:** fixable within the chain, but only by a global rule, not a per-route patch: *after `sig_C`, anchor at `C`*. Equivalently, the processors should not consult `declarationAnchor(m)` at all once a signature substitutor is in play; the signature map's class is the anchor.

### (c) Refinement and anonymous-class members: no class anchor

`lazy val reifier: Reifier { val global: Utils.this.global.type }` (`reify/utils/Utils.scala`). Selecting `reifier.global` resolves `global` to the refinement's declaration, whose `nameContext` is not a `PsiMember` of a class, so `declarationAnchor` is null and the link runs the anchorless walk. scalac gives the refinement a refinement class symbol `R` as `owner(global)`, with `owner(R)` = the enclosing class, and `matchesPrefixAndClass` has an explicit `isRefinementClass` arm (`pre.widen.typeSymbol isSubClass clazz`). The owner chain exists; IntelliJ just has no symbol to hang it on.

**Verdict:** fixable, by synthesizing the anchor: treat a refinement member as owned by a virtual class whose owner is the enclosing class of the compound type's occurrence, and make the walk's `baseType` step for that virtual class succeed when `target` widens to a compound containing the refinement. Until then this route is a heuristic, and `null` anchor should be treated as scalac's unmatched case (follow-up 2 in the investigation comment), not as "narrow by inheritance".

### (d) Sibling-trait members spelled after the declaring trait

Inside `trait Definitions { self: SymbolTable => }`, a use of `Symbol` is spelled by scalac as `Definitions.this.Symbol` (the self type lets `Definitions.this` see `Symbols`' members, and `memberType` from `Definitions.this` gives `Definitions.this.Symbol`). IntelliJ resolves it to the declaration in `Symbols` and spells it `Symbols.this.Symbol`.

This is not an `asSeenFrom` bug. It is a different choice of *which prefix* a member found through a self type is viewed from: scalac uses the use site's this (`Definitions.this`), IntelliJ keeps the declaring trait's this. Downstream, every `asSeenFrom` of that type then has to be told that `Symbols.this` is reachable from a `Definitions` cursor, which is exactly what the self-type allowance did, and which case (a) showed to be unsound in general (it also admits `Importers.this` from a `Types` cursor through `SymbolTable`).

The two spellings are equivalent only under the assumption that `Definitions.this` and `Symbols.this` are the same instance, which the branch deliberately does *not* assume (§5 of the parity notes, corpus 28), and which scalac does not assume either: scalac never produces `Symbols.this.Symbol` inside `Definitions`, so it never has to decide.

**Verdict:** intrinsic to the chain as long as resolution through a self type keeps the declaring trait's this-type. The TypeDefinitionMembers fix for SCL-7008 (a member that `C` itself has takes `C`'s signature substitutor) is the right shape generalized: a member reached from `C.this` through `C`'s self type `S` should be viewed as `A(C.this, S)(sig_S(m))`, which spells it `C.this.Symbol`. That is scalac's rule, and once it holds, the self-type allowance in owner-chain matching has nothing left to do.

## 7. Verdict: sound in principle, heuristic in practice

**The chain architecture is sound in principle.** §5 gives the conditions under which a chain is a staged `asSeenFrom`, and they are statable as local invariants on each link. Nothing about fused recursive updates, cached signature substitutors, or composition through `followed` is inherently wrong; scalac itself stages `asSeenFrom` through `baseType`, which is a cached view.

**The current construction is a heuristic.** None of the four conditions is enforced, and three of the four failures above are violations of them: wrong anchor (a, b), link applied to non-member types (a), anchorless walk (c). Every cake-specific allowance on the branch (`selfTypeReaches`, `targetDenotesLeafClass`, the "cursor inherits D" early exit, no self-embedding) exists to compensate for a condition that is violated somewhere upstream. Each allowance is a shortcut through the owner chain that is correct for the case that motivated it and admits other rewrites that scalac rejects; (a) is the proof. The pattern "add an allowance, then find the case it over-admits, then add a gate" will not converge, because the allowances are answering a question (`is D.this reachable from this cursor?`) whose correct answer depends on information the link no longer has: what view its input is in.

**(d) is the one intrinsic case**, and it is intrinsic to *resolution*, not to the chain: the chain cannot compute the scalac spelling because it is handed the wrong starting prefix.

## 7.1 Formal check

The composition law and the chain theorem are proved in Lean 4 at this directory (`Chain.lean`: `compose`, `chain_is_single`, `idempotent`), over an abstract world of base-type facts with one axiom, lockstep (`asSeenFrom` commutes with `baseType.prefix`). `IntelliJ.lean` models the narrow-against-target fallback and proves `agrees`: IntelliJ's walk equals scalac's wherever the fallback does not fire. `Cases.lean` checks (a) and (b) by computation: for (b) the mis-anchored chain is `asf(MatchTranslator.this, MMI)`, the well-anchored one is `asf(TreeMakerWarnings.this, MMI)` = scalac; for (a) the fallback rewrites `Importers.this` to `from` where scalac's walk leaves it alone.

One correction the formalization forced on §6(a): the value-projection route is not an I1 violation in the walk's own terms, it is I3. With anchor `StandardImporter` and target `from`, scalac's walk finds no `from baseType StandardImporter`, runs out of prefix and stops; IntelliJ's walk takes the fallback. Anchoring at each member's owner (the WIP fix) avoids the fallback rather than correcting a wrong cursor.

`Chain.lean` also names three structural constraints a runtime assertion can check without the type being substituted: C1 `wellAnchored` (each link anchored at the class of the running composed prefix; then `chain_is_intended`, the chain views from the intended prefix), C2 `fixedTarget` (a link doesn't rewrite its own target; then `idempotent_of_fixed` and `dedup`, so duplicates in `followed` chains can be dropped), C3 `stateSafe` (a substitutor threaded into resolve state has no this-links; then `stateSafe_preserves_this`). C2 and C3 are free at runtime; C1 needs the running prefix, so it is a test-flag check in `followed`. The cheap form of C1, "each anchor is the class of the previous link's target", is exact only when the previous link rewrote the running prefix to its own target, which is the `sig_C >> fromType` shape.

Not proved: that `BaseTypes.baseType` satisfies lockstep (an axiom; the TCK's baseType dimension is its empirical check), and termination of the fused engine with results re-entering resolution. `chain_is_single` says that under I1 to I3 no output ever needs re-rewriting, which is the statement that matters for the brake.

## 8. What to do

Two options. The first is the minimal set of invariants; the second removes the need for most of them.

### 8.1 Minimal invariants for the chain

- **I1 (anchor = view).** A `ThisTypeSubstitution` link is constructed with `seenFromClass` = the class whose view its input is in. Concretely: a link following `sig_C` is anchored at `C`; a link following another this-link with target `t` is anchored at `cls(t.widen)`; the first link on a raw declared type is anchored at `owner(m)`. `substitutorWithThisType(declarationAnchor(m))` is wrong whenever a signature substitutor precedes it, and that is the common case.
- **I2 (member infos only).** This-type links live in the substitutor of a resolve result and are applied to that result's declared type. They are not threaded into resolve *state* for other references. `matchClauseSubstitutor` keeps its type-parameter bindings and drops its this-type links, or carries them only as the substitutor for the pattern's own bound variables.
- **I3 (faithful walk).** `seenFromClass == null` is scalac's unmatched case: leave the this-type alone (after synthesizing anchors for refinement members per (c)). Remove `selfTypeReaches` (done in WIP), then `targetDenotesLeafClass` and the narrow-against-target fallback once their motivating tests pass without them; each is a shortcut past I1.
- **I4 (no re-entry).** With I1 to I3, `embedsRewrittenThis` should never fire. Keep it as an assertion-level diagnostic, not as semantics.

How to check them:

- In `ThisTypeSubstitution`, under a test-only flag, assert on each firing that `seenFromClass` is non-null and that when the rewrite is *refused* by owner-chain matching the this-type's class is not on `seenFromClass`'s owner chain by any route (a refusal where it *is* on the chain means an upstream link was mis-anchored). Log the chain's `toString` on violation; the firing census tooling at tag `scala-typesystem-tck-pre-cleanup-2026-10-06` already does most of this.
- In `ScSubstitutor.followed`, under the same flag, check that a `ThisTypeSubstitution` whose predecessor in the array is a `ThisTypeSubstitution` with target `t` is anchored at `cls(t)`, and that one following a `SuperTypesData` signature map for `C` is anchored at `C`.
- Differential: the TCK `termType` probes already compare `pre.memberType(m)` spellings with scalac. Add corpus entries for each of (a) to (d) (the `Importers`, `MatchWarnings`, `Utils.reifier`, and `Definitions`/`Symbols` shapes are small), so each invariant has a row that fails when it is violated.

### 8.2 Restructuring: compute `memberType` once

The alternative is to stop composing and compute what scalac computes: `memberType(pre, m) = A(pre, owner(m))(declaredType(m))` as a single operation at the point of resolution, with the signature substitutor used only to *find* `m` (override resolution, which `MixinNodes` does well) and not to *type* it. Then:

- There is one anchor per selection and it is `owner(m)`, which is always known. I1 holds by construction.
- Resolve results carry `(m, pre)` instead of `(m, subst)`, and the type is derived. Nothing to thread into state, so I2 holds; `matchClauseSubstitutor` becomes type-parameter-only.
- `ThisTypeSubstitution` has exactly one caller shape and can be a faithful `thisTypeAsSeen` over `BaseTypes.baseType` with no fallbacks; I3 and I4 hold.
- (d) is fixed at the source: a member found through `C`'s self type is `memberType(C.this, m)`, spelled `C.this.Symbol`, because `pre = C.this` is the use site's prefix regardless of where `m` was found.

The cost is that the inherited-member view (`sig_C`) is no longer precomputed per class; scalac pays the same cost and amortizes it with `baseType` caching and `typeAsMemberOf`. `ScProjectionType.actual` is already the beginning of this: it computes the override-aware member and its view from `projected` in one place. The spike `spike/single-member-type` consolidated several hand-written copies onto it. The restructuring is that direction carried through to the resolve processors.

### 8.3 Recommendation

Do 8.1 first; it is incremental, each invariant has a test, and I1 alone (anchor at `C` after `sig_C`, globally rather than per route) is the fix for (b) and removes the reason for the self-type allowance. Treat 8.2 as the target shape, and move each processor onto a single `memberType(pre, m)` as its allowances are removed. The TCK's `termType` dimension is the differential check for both: every invariant violation shows up as a spelling difference against scalac, and the corpus should gain one entry per case in §6 before either change lands.
