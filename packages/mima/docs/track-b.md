# Track B — binary compatibility (`BinCompat/`)

## Problem

Zinc asks whether a client must be *recompiled*; MiMa asks whether its old classfile still *links*. With JVM linkage written as a `Task` (Track J), both are questions about a trace against an edited environment, so the Zinc framework's vocabulary (keys, coverage, abstraction) should describe MiMa too. Two questions follow:
- Is MiMa sound, and where it isn't, why? MiMa had never been checked against a model of the JVM.
- How do Zinc and binary compatibility relate? The expectation: Zinc-clean implies binary-compatible for a client, and the converse fails exactly where MiMa is needed.

## What was built

- **[`packages/mima/probes/Mima.scala`](../probes/Mima.scala)** runs `mima-core` 1.2.1 (pinned, via scala-cli) on class directories: the `v0`/`v1` that [`packages/jvm/probes`](../../jvm/probes) renders, and, for Scala, [`packages/mima/probes/scala.sh`](../probes/scala.sh) compiles each [`packages/scala/Scala/Catalogue.lean`](../../scala/Scala/Catalogue.lean) case with scalac 2.13.18.
- **[`packages/mima/MiMa/Mima.lean`](../MiMa/Mima.lean), a model of MiMa's checker** (`Analyzer`, `TemplateChecker`, `FieldChecker`, `MethodChecker`), read from its sources.
- **[`packages/mima/MiMa/Edits.lean`](../MiMa/Edits.lean), an edit space:** every well-formed single edit of two base libraries, changing one class's header (abstract, final, interface, public, superclass, interfaces) or setting one member slot (`m()V`, `m()I`, field `m`) to absent or any combination of flags. 302 edits. The client space `spaceB` is [`Jvm.Clients.space3`](../../jvm/Jvm/Clients.lean#L79) plus `X implements J`, `X implements I, J` and `m()I` sites.
- **[`packages/mima/MiMa/Keys.lean`](../MiMa/Keys.lean), MiMa as a bridge design** in [`docs/specification.md`](../../../docs/specification.md)'s terms. `mima o n` is `(keys o).flatMap (check o n)`, with keys per class public in the old library (`template c`, `field c n d`, `method c n d`, `newMethods c`) and `covers` saying which class-table entries each key's comparison reads. The obligation: if no key reports, every client that linked against the old library still links. MiMa compares by a relation, not equality (an added method is a changed answer, and fine), so abstraction here means "strong enough for linking".
- **[`packages/mima/MiMa/Fixed.lean`](../MiMa/Fixed.lean), a corrected rule set,** and [`packages/mima/MiMa/Sound.lean`](../MiMa/Sound.lean), its check on the space.
- **`BinCompat/ZincBridge*.lean`, the Zinc ⇒ binary-compatible theorem** (Track B4) and its variants.

Steps:
- Track B1: MiMa against the catalogue and the edit space. Done.
- Track B2: MiMa as keys; its gaps; corrected rules checked on the space. Done; a proof for all libraries is open.
- Track B3: source-level spaces. Started; open.
- Track B4: Zinc-clean implies binary-compatible. Done.

## Results

### The model of MiMa agrees with MiMa (Track B1)

As a multiset of problems per library, on every `Jvm` catalogue case (Tracks J1–J3, J5 and J6) and every edit of the edit space ([`packages/mima/probes/compare.py`](../probes/compare.py), last run on 12 October 2026). On the catalogue the first problem MiMa reports is each case's `mima` field, checked against the model by kernel `decide`; two expected names were wrong before (`defaultRemoved` gets `DirectAbstractMethodProblem`, `superCallAbstract` gets `AbstractClassProblem`). The cases with no expected problem (`mima := none`) are silent in MiMa itself, not only in the model.

Running the J5 cases found one model bug: the model looked constructors up in superclasses, so `ctorPulledUp` (a constructor moved from `B` up to `A`) was silent. MiMa's `ClassInfo.lookupClassMethods` does not inherit constructors, as it does not inherit static methods, and reports `DirectMissingMethodProblem`; the model now does the same.

Per edit, MiMa's report against `breaksSomeClient`:

| MiMa | some client breaks | only changes behaviour | neither |
|---|---|---|---|
| reports | 140 | 0 | 17 |
| silent | **40** | 4 | 101 |

- **The 40 false negatives** all break on HotSpot 21, 25 and 27 (each edit's breaking client, run by [`packages/jvm/probes`](../../jvm/probes)). They fall into four gaps, below.
- **The 17 reported edits that break no client** are all `ReversedMissingMethodProblem` (a new abstract method). It is reachable only through library code calling it on a client's subclass, and the model has no library method bodies (Track J4), so they are outside the client space, not false positives.
- **The 4 silent edits that change behaviour** (a new override in `B`, a field in `B` hiding `A`'s) are outside MiMa's scope.

### Why MiMa misses: coverage and abstraction gaps (Track B2)

[`miss_changes_footprint`](../MiMa/Keys.lean#L71) (from [`link_congr`](../../jvm/Jvm/Link.lean#L578)): a client that stops linking has a footprint query whose answer changed. So every miss is either a **coverage gap** (no key covers the changed query) or an **abstraction gap** (a key covers it and passes). Each gap has a witness in [`packages/mima/MiMa/Keys.lean`](../MiMa/Keys.lean) (library edit, client, changed query) by kernel `decide`, confirmed on HotSpot, with MiMa silent.

| Gap | Witness | Edit | Client failure | Kind |
|---|---|---|---|---|
| MiMa-F1, final fields | `finalField` | a public field becomes `final` | `putfield`/`putstatic`: `IllegalAccessError` | abstraction: the field key covers it, and `final` is not compared |
| MiMa-M1, shadowing through a subclass | `shadowStatic`, `shadowField`, `overridePrivate` | `B extends A` gains a member named like an inherited one, with any access and any of `static`/`final`; or `B`'s override becomes private | `invokevirtual B.m` / `getfield B.m`: ICCE, `IllegalAccessError`, or a final override at load | coverage: MiMa checks only members a class declares. When `B` declared it, abstraction instead: MiMa's parser drops private members and its lookup finds `A.m` |
| MiMa-F2, interface fields first | `ifaceField` | an interface gains a field | `X extends A implements I` resolves `X.m` to `I.m` (superinterfaces before superclass) | coverage: MiMa's field lookup never reads interfaces |
| MiMa-D1, conflicting defaults | `defaultConflict` | an interface gains a default another public interface has | `invokeinterface`: ICCE | coverage: `checkNew` reads only abstract methods |
| MiMa-P1, protected members | `protectedRemoved` | a protected method is removed | a subclass client's call: `NoSuchMethodError` | coverage: only `ACC_PUBLIC` members get keys |

MiMa-P1 is outside the edit space (the bases have no protected member), hence its own witness. Scala's `protected` is public in bytecode, so it affects Java-defined libraries.

**The corrected rules** ([`packages/mima/MiMa/Fixed.lean`](../MiMa/Fixed.lean)) are MiMa plus: the member a reference *through* each public class resolves to, by JVM resolution with private members and superinterfaces, compared by access rank, `static`, `abstract` and `final`, for methods and fields (MiMa-M1, MiMa-F1); an interface that newly sees a field (MiMa-F2); a new default that an unrelated public interface also has (MiMa-D1). On the space they report all 40 false negatives and nothing that breaks no client beyond MiMa's own 17. [`packages/mima/MiMa/Sound.lean`](../MiMa/Sound.lean) checks by kernel `decide` that every unreported edit leaves every client of `spaceB` linking: 105 edits against the full client space, about 30 minutes and 7 GB, so it is built on demand (`lake build MiMa.Sound`).

**Package-private members are out of scope.** Track J6's `methodBecomesFinalBehind` makes a package-private `A.m` final behind a public `B.m` in another package, and breaks a client class in `A`'s package that overrides both. MiMa is silent, and so are the corrected rules (kernel `decide` in [`Fixed.lean`](../MiMa/Fixed.lean)): through `A` the method is package-private, which no key covers, and through `B` it resolves to `B.m`, which is unchanged. A package-private member is visible only in its run-time package, so the clients it can break are classes another JAR adds to the library's package, a split package. We take that as a scope line, not a sixth gap. Over the same edit on every library of the chain space, whose clients are outside the library's packages, every break the corrected rules miss has a library that no longer loads by itself, since one of its own classes now overrides the final `A.m` (`lake exe bincompat finalBehind`).

Not proved: soundness of the corrected rules for all libraries ([`docs/roadmap.md`](../../../docs/roadmap.md)). The equality design (every query a key, compared by equality) is sound for all libraries by [`link_congr`](../../jvm/Jvm/Link.lean#L578), but reports every edit.

### Source-level spaces, started (Track B3)

The Scala catalogue cases of Tracks S1–S3, compiled by scalac 2.13.18 and run through MiMa: MiMa reports exactly the cases where the old client fails against `v1`.
- `abstractAddedToTrait`, `valAddedToTrait`: `ReversedMissingMethodProblem` (for the `val`, the getter and the mangled setter).
- `classBecomesTrait`: `IncompatibleTemplateDefProblem`.
- `paramWithDefaultAdded`: `DirectMissingMethodProblem`.
- `widenedToValueClass`: `FinalClassProblem`, `DirectMissingMethodProblem` (the constructor), `IncompatibleMethTypeProblem`.
- Silent on `concreteAddedToTrait` (compatible) and `traitOverrideAdded` (links, but runs `B.m` where a fresh build runs `T.m`; outside MiMa's scope).

### Zinc-clean implies binary-compatible (Track B4)

**The front end.** Scala lowering is an [`XCompiler`](../../inc-comp/IncComp/General.lean#L22) ([`General.lean`](../../inc-comp/IncComp/General.lean)): a unit is a source unit, its task is `lowerSrc` with queries renamed to `(unit, side)`, its output the unit's declarations plus its classfiles. The interface is the declaration, so it is source-determined. Every query is answered as if in the same run (`inRun = true`), faithful for Scala 2.12 and 2.13. A key per traced query, hashed by the declaration it read, meets the obligations (`searched_obligations`).

**[`XCompiler.untouched_eq_clean`](../../links/Links/ZincBridge.lean#L132)** ([`packages/links/Links/ZincBridge.lean`](../../links/Links/ZincBridge.lean)). After an edit, if Zinc's loop stops and a unit was in none of its rounds, its old output equals its output in the clean build of the new sources. Hypotheses: the framework's `Obligations`; source-determined interfaces (the explicit-interface case of T3b); a `Sound` policy inside `S`; the dirty set in the first round; the old build up to date except at the edit ([`inv_of_edit`](../../links/Links/ZincBridge.lean#L118)). [`must_recompile`](../../links/Links/ZincBridge.lean#L149) is the contrapositive. For lowering, [`after_eq_fresh`](../../links/Links/ZincBridge.lean#L277): the client's old classfiles with the new library give the same [`Jvm.outcome`](../../jvm/Jvm/Link.lean#L569) as a fresh build, and [`compatible_of_untouched`](../../links/Links/ZincBridge.lean#L297): [`Jvm.Compatible`](../../jvm/Jvm/Link.lean#L585) holds whenever the fresh build links.

**The converse fails** ([`gap_witness`](../../links/Links/ZincBridge.lean#L331)). Adding a concrete method to a trait leaves the old `X extends T` linking (it selects the default method), so the edit is binary compatible; but a fresh build adds a mixin forwarder, so `X`'s classfile changes and every sound bridge recompiles it. That gap is what MiMa does not report.

**Scala 3, compiled separately** ([`packages/links/Links/ZincBridgeScala3.lean`](../../links/Links/ZincBridgeScala3.lean)). A round reads the rest from TASTy, so the faithful compiler answers `inRun := v ∈ G`. Under F6 the obligation that fails is `comp`: `C extends T`, `T` holding only a `lazy val`, gets different classfiles in `{T, C}` and `{C}` over the same interfaces ([`f6_witness`](../../links/Links/ZincBridgeScala3.lean#L67)), so no per-unit task makes `comp` hold, whatever the keys ([`not_comp`](../../links/Links/ZincBridgeScala3.lean#L79)). With [retronym/scala3#10](https://github.com/retronym/scala3/issues/10) (the TASTy reader computes `NoInits` as the namer does) the faithful joint compilation is Track B4's ([`group3Fix_eq`](../../links/Links/ZincBridgeScala3.lean#L102)), and Track B4 holds for Scala 3 ([`after_eq_fresh_fix`](../../links/Links/ZincBridgeScala3.lean#L110)). We take the fix over restricting to programs without the F6 shape: that restriction covers every trait the client reads, library traits included, and excludes common code.

**Zinc's actual keys** ([`packages/links/Links/ZincBridgeKeys.lean`](../../links/Links/ZincBridgeKeys.lean)): inheritance on each parent hashed over its ancestors, member-ref name keys on every class the source names, and the unit itself. **Coverage fails** ([`coverage_fails`](../../links/Links/ZincBridgeKeys.lean#L149)): for `T { def f(v: V): Int }` and `object O extends T`, lowering `O` erases `f` for its forwarders and so asks for `V`, which `O`'s source never names and which is not an ancestor. **The conclusion fails too** ([`loop_witness`](../../links/Links/ZincBridgeKeys.lean#L158)): `V` becomes a value class, Zinc recompiles `V` then `T`, `T`'s API is unchanged, the loop stops with `O` untouched, and a fresh `invokestatic O.f(I)I` gets `NoSuchMethodError`. The fixes: keys on value classes in inherited signatures (what `searched` does), or hashing a value-class reference by its underlying type. A JVM-linkage theorem predicted a Zinc bug; the pending scripted tests in [retronym/zinc#57](https://github.com/retronym/zinc/issues/57) reproduce it.

**Library JARs** ([`packages/links/Links/ZincBridgeLibs.lean`](../../links/Links/ZincBridgeLibs.lean)). A library has no Analysis, so each query on a library unit is covered by the unit's stamp key, hashed by its whole interface ([`stamp_covers`](../../links/Links/ZincBridgeLibs.lean#L63)); the bridge meets the obligations (`obligations`). [`library_client`](../../links/Links/ZincBridgeLibs.lean#L107) is T5a (`inv_external`) followed by [`untouched_eq_clean`](../../links/Links/ZincBridge.lean#L132): a client the loop never recompiled links against the edited JAR as a fresh build does, given a disjoint library, an up-to-date old build, stored stamps that are the old library's interfaces ([`fresh_of_stamps`](../../links/Links/ZincBridgeLibs.lean#L91)), and a sound policy.

Not done: a restricted Scala 3 theorem without the fix. [`XCompiler`](../../inc-comp/IncComp/General.lean#L22) subsumes the [`NCompiler`](../../inc-comp/IncComp/NonLocalAns.lean#L34) statement first planned (through [`NCompiler.toX`](../../inc-comp/IncComp/NonLocalAns.lean#L73)).

## Issues filed

Filed against scala-garden/mima on 12 October 2026, each with a reproducer in Java checked on HotSpot 21 and MiMa 1.2.1:

1. MiMa-F1, a field that becomes `final`: [scala-garden/mima#993](https://github.com/scala-garden/mima/issues/993).
2. MiMa-M1, a member a subclass adds breaks clients of an inherited one: [scala-garden/mima#994](https://github.com/scala-garden/mima/issues/994). Filed for the cases javac can produce: a new field that hides an inherited one (private or static), and a new `final` override. The method-hiding cases of the model (a static or private `m()` in the subclass) cannot come from javac when both classes compile together, so the issue only mentions them.
3. MiMa-F2, a field added to an interface hides a superclass field: [scala-garden/mima#995](https://github.com/scala-garden/mima/issues/995). The reproducer needs no client class of its own: a library class extending `A` and implementing `I` is enough.
4. MiMa-P1, protected members of Java classes are not checked: [scala-garden/mima#996](https://github.com/scala-garden/mima/issues/996).

Not filed: MiMa-D1, a new default that conflicts with another interface's. It reproduces (`IncompatibleClassChangeError: Conflicting default methods`), but the conflict exists only in a client class that implements both interfaces. MiMa compares two versions of one library, class by class, and does not check interactions between unrelated classes; this gap belongs to a migration manager that also had data on how clients use the library.

## PRs

- [retronym/talks#64](https://github.com/retronym/talks/issues/64): MiMa against the `Jvm` model, the gaps, the corrected rules (Tracks B1, B2).
- [retronym/talks#59](https://github.com/retronym/talks/issues/59): Zinc-clean implies binary-compatible, and the converse fails (Track B4).
- [retronym/talks#62](https://github.com/retronym/talks/issues/62): Track B4 for Scala 3 separate compilation, Zinc's actual keys, and library JARs.
