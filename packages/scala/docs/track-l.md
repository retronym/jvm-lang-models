# Track L — Laziness in the compiler: cycles, levels, phases

20 October 2026.

## Summary for a busy reader

A Scala compiler is a lazy evaluator. Its symbol table is a set of *facts* — a symbol's info, its parents, its members' signatures, its name and flags at a phase — each computed on demand by a *completer* and then cached. Laziness is not an optimisation layered on a strict semantics: it is what lets a program whose definitions refer to each other be checked at all. A cyclic reference error is the evaluator re-entering a fact it is still computing.

The model ([`Query.Lazy`](../../query/Query/Lazy.lean), [`Query.Freeze`](../../query/Query/Freeze.lean), [`ScalaTypes.Laziness`](../../scala-types/ScalaTypes/Laziness.lean)) says five things, each proved or checked:

1. **If a program's definitions are well-founded, lazy forcing never cycles, in any order** ([`force_ok`](../../query/Query/Lazy.lean#L111), [`forceAll_ok`](../../query/Query/Lazy.lean#L160)). Well-founded here allows recursion through a *name* (`class C extends Ord[C]`); it forbids recursion through a *value* (`def f = g; def g = f`).
2. **A cycle is true or spurious.** True: the program's own definitions are circular, and no compiler can avoid the error. Spurious: the program is well-founded, but the compiler computes a *bundle* of facts where it needed one, and the bundle contains the asker. Four of the twenty-four battery programs are well-founded, accepted by dotc and rejected by scalac (one of them crashes 2.13.18). Which definitions count as "the program's own" is the specification's call, and for an overriding method's inferred type the SLS and both compilers disagree (`ir2`).
3. **Facts come in levels.** What a symbol is (name, kind, most flags), what a class is made of (type parameters, parents, member *names*), and what its members are (signatures, inferred types). A completer may ask at most the first two levels of a fact still being completed. dotc writes the levels into the code (`FromStartFlags`, `AfterLoadFlags`, `TempClassInfo`); scalac leaves them implicit, and the spurious cycles are where it bundles levels together.
4. **Some facts are pushed, not pulled.** A sealed class's children grow as subclasses are entered; a read sees whatever has arrived. Guarded by a freeze (a read forbids later pushes), the answer is either the whole fact or a hard error, whatever the order ([`guarded_quasi_det`](../../query/Query/Freeze.lean#L67)); unguarded, it is silently order-dependent ([`unguarded_diverges`](../../query/Query/Freeze.lean#L105)).
5. **Facts are indexed by phase.** A symbol's info at typer differs from its info at erasure; its name before LambdaLift differs from after. Phase-indexed laziness is sound when no fact reads a later phase ([`phase_ranked`](../../query/Query/Lazy.lean#L199)). dotc keeps every version of every fact; scalac versions the info and masks the flags but overwrites the name and owner, so a typer-phase question asked late gets a late answer. Measured: three typer-phase answers change after a run in scalac 2.12.21 and 2.13.18, none in dotc 3.9.0.

And, measured: the converse fails in practice. A program whose implicit search skips a candidate being completed compiles in one file order and not the other in scalac 2.12 and 2.13, and an incremental build rejects what the clean build accepted; in dotc 3.9 a wildcard export silently leaves out a member whose type is being inferred, so the same sources compile to different public members by file order, and mutual wildcard exports compile in one file order and not the other (§6).

The rest of this note explains each idea, maps it onto both compilers' code, and gives the evidence and the probes that produced it.

## 1. A compiler is a lazy evaluator

A fact has a rule: a computation that asks other facts (a [`Query.Task`](../../query/Query/Task.lean#L12)). Forcing a fact runs its rule once and stores the result; forcing it again reads the store. Forcing a fact that is on the stack of facts being forced is a black hole. That is all [`Query.Lazy.force`](../../query/Query/Lazy.lean#L55) is, and it is all a completer framework is:

| | scalac 2.12 / 2.13 | dotc 3 |
|---|---|---|
| a fact not yet computed | `Symbol.info` holding a `LazyType` | `SymDenotation.info` holding a `LazyType` |
| forcing it | `Symbol.info` → `completeInfo()` → `LazyType.complete(sym)` | `SymDenotation.info` → `completeFrom(completer)` |
| the black hole | the `LOCKED` flag: set on entry, a second entry throws `CyclicReference` | the `Touched` flag: same |
| the phase a completer runs at | `phaseOf(infos.validFrom)`: the phase it was installed at, not the caller's | `atPhase(validFor.firstPhaseId)`: same |
| a body typed early to infer a type, reused later | `typer.transformed` | the `TypedAhead` attachment |
| the chain that closed a cycle | `-Vcyclic` (2.13) | `-explain-cyclic`, `-Ydebug-cyclic` |

**The theorem.** Say a *semantics* for the rules is a valuation `ρ` that is a fixed point (each fact is what its rule computes from the others: `Fix`) and a rank that strictly decreases along every fact a rule asks under `ρ` (`Ranked`). Then [`force_ok`](../../query/Query/Lazy.lean#L111): forcing any fact, from any store that agrees with `ρ`, returns its value under `ρ` and never black-holes; and [`forceAll_ok`](../../query/Query/Lazy.lean#L160): any order of demands gives the same answers. The compiler's answer to a well-founded program does not depend on which file it typechecks first. Conversely ([`cycle_unranked`](../../query/Query/Lazy.lean#L176)), a black hole means these rules have no ranking with the fact low enough.

The ranking runs over the facts a rule *asks*, not over everything its answer mentions. That is what makes F-bounds, recursive classes and `List[+A] { def tail: List[A] }` fine: the recursion goes through a type constructor or a `TypeRef`, a reference by name, and asking for a name asks nothing. Recursion becomes an error only when a *strict* consumer looks through the name — base classes, dealiasing, bounds checking, member lookup — at a fact still being computed.

## 2. True and spurious cycles

A compiler does not force a program's semantic facts one by one. It forces its own facts, each of which bundles several semantic ones: a class's whole info, every member's signature for overloading resolution, every member of a prefix for a wildcard import. A bundle that contains the asker black-holes even when the semantic facts are well-founded. So:

* **True cycle**: the semantic rules have no ranking. Every compiler must reject the program; the only cure is an annotation.
* **Spurious cycle**: the semantic rules are ranked, and the compiler's bundling is not. Another compiler, or a finer cut of the same one, accepts the program.

[`ScalaTypes.Laziness`](../../scala-types/ScalaTypes/Laziness.lean) gives each shape three times — the semantic rules (ranked), scalac's bundling, dotc's:

* **A parent that reads the class's own member** (`class C extends B[C#T] { type T = C }`): the semantic rules are ranked ([`fine5_ranked`](../../scala-types/ScalaTypes/Laziness.lean#L62)). scalac completes parents and members as one `ClassInfoType`, typing the parents first, so looking up `C#T` needs the info being computed: no ranking at all ([`scalac5_unranked`](../../scala-types/ScalaTypes/Laziness.lean#L166)). dotc's class completer first installs a `TempClassInfo` with the indexed members, then types the parents, and succeeds ([`dotc5_ok`](../../scala-types/ScalaTypes/Laziness.lean#L90)). Real compilers: scalac 2.12.21 and 2.13.18 report the cycle, dotc 3.9.0 compiles it.
* **A consumer of every member's signature**: `n`'s completer asking `m`'s signature is fine; asking every member's (`members.map(_.info)`, the shape of overloading resolution and implicit search over a scope) includes `n` itself ([`allSigsM_cycles`](../../scala-types/ScalaTypes/Laziness.lean#L122)). Both compilers, measured below.
* **The specification decides** (`trait T { def m = new C().m }; class C extends T { override def m = 1 }`). By the SLS an inferred result type is the type of the right-hand side, so `C.m : Int` asks nothing and the program is well-founded ([`slsI_ranked`](../../scala-types/ScalaTypes/Laziness.lean#L150)). scalac types an overriding method's right-hand side against the overridden method's result type, and dotc (with scalac under `-Xsource:3 infer-override`) takes the type from it outright; under their rules `C.m` asks `T.m` and the cycle is true ([`implI_unranked`](../../scala-types/ScalaTypes/Laziness.lean#L158)). All three compilers reject it.

**The signature of a spurious cycle is order sensitivity.** A true cycle fails under every demand order. A spurious one can come and go with an irrelevant edit, a change of file order, joint versus separate compilation, or an incremental build versus a clean one. Where a compiler *avoids* a cyclic reference by skipping the fact (scalac's implicit search leaves out a candidate whose symbol is being completed: `ImplicitInfo.isCyclicOrErroneous` reads its `LOCKED` flag), the cycle becomes an absence and the *answer* depends on the order — no longer an error you would rather not see, but a loss of determinism. [Phase 15](../../zinc/docs/15-cycles.md) ([`two_fixpoints`](../../zinc/Zinc/Loop/Cycles.lean#L196)) is that loss reaching Zinc.

## 3. Levels of knowledge

The cure for spurious cycles is to let a completer ask *part* of a fact still being computed. Three levels:

| level | what | who may ask it of a symbol still completing |
|---|---|---|
| 0 | existence, name, kind, most flags | anyone, always |
| 1 | type parameters, parents, the *names* of members | a completer, if the symbol publishes them early |
| 2 | members' signatures, inferred types, base types | only once the symbol is complete |

Namer's contract is to produce level 0 and nothing else; every place Namer forces more (case-class synthetics, Scala 3 `export` forwarders, Scala 2 macro annotations) is where spurious cycles live. How each compiler implements the levels, measured by the forcing probes below:

| | scalac | dotc |
|---|---|---|
| level-0 flags without completing | raw flags read without completing: never a cycle, but a flag a completer would set is silently absent | `SymDenotation.isCurrent(fs)`: a flag in `FromStartFlags` (or `AfterLoadFlags` once loaded) is answered without completing; any other flag forces, and from inside the completer is a `CyclicReference` |
| type parameters early | `PolyTypeCompleter` publishes them before the rest; without it, `typeParams` inside the completer is silently empty | without an early publication, `typeParams` inside the completer is a `CyclicReference` |
| member names before parents | no: one completer types the parents, then enters the members | `TempClassInfo`: members indexed first, parents typed against it |
| member lookup | `member(m)` finds the symbol without its info | `member(m)` builds a denotation and forces `m`'s info |

The pattern: dotc declares its levels and fails loudly when they are violated; scalac's are implicit, and a violation is either a cycle or a silently wrong answer.

## 4. Facts that are pushed

A sealed class's children, a companion's link to its class and the implicits registered in a scope are not computed by a completer; they grow as other definitions are entered. A read sees whatever has arrived. scalac's `knownDirectSubclasses` was empty or partial depending on file order ([scala/bug#7046](https://github.com/scala/bug/issues/7046), #7588, #8776, #10454); dotc's `Mirror.SumOf` failed across files ([scala/scala3#9069](https://github.com/scala/scala3/issues/9069)).

The repair is a freeze: a read marks the fact queried, and a later push is a hard error. dotc's `ChildrenQueried` flag ("children of … were already queried before … was discovered"); scalac's `KnownDirectSubclassesCalled` attachment, which `addChild` turns into a `globalError` ("knownDirectSubclasses of … observed before subclass … registered") until typer ends. In [`Query.Freeze`](../../query/Query/Freeze.lean) that is an LVar freeze, and it buys *quasi-determinism*: a run either completes with every read seeing the whole fact, whatever the order ([`guarded_quasi_det`](../../query/Query/Freeze.lean#L67)), or fails loudly ([`guarded_fails`](../../query/Query/Freeze.lean#L110)); without it, two schedules give one read two answers and nothing fails ([`unguarded_diverges`](../../query/Query/Freeze.lean#L105)). Both compilers also complete the producers before the first read, so the pushes happen first: dotc completes every class that could be a child ([scala/scala3#9083](https://github.com/scala/scala3/issues/9083)); scalac's `knownDirectSubclasses` calls `forceDirectSuperclasses` on every class of the same package in the same source file, which, despite its name, initialises every definition in each class's tree (`Namers.TypeCompleter`), a coarse bundle. [scala/scala#11298](https://github.com/scala/scala/issues/11298) (open) takes the fine road for sealed *Java* classes: permitted subclasses become children without being forced, since JLS §8.1.6 makes them direct subclasses. A freeze can also fire wrongly: a read inside speculative typing that is later discarded still froze the fact ([scala/scala3#18484](https://github.com/scala/scala3/issues/18484)), the push-side twin of a spurious cycle.

## 5. Facts indexed by phase

Every fact is asked *at a phase*: `enteringPhase`/`exitingPhase` in scalac, `atPhase` in dotc. The info of `def m(x: Int)(y: Int): Int` is curried at typer and `(x: Int, y: Int): Int` after uncurry; a local `class L`'s name is `L` at typer and `A$L$1` after flatten. The later version is computed lazily from the earlier one by a transformer, when a later phase first asks:

| | scalac | dotc |
|---|---|---|
| versions of the info | `TypeHistory` (`validFrom`, type), extended forward by `transformInfos` with each phase's `InfoTransformer`; reading at an earlier phase walks back | the `nextInRun` chain of denotations, each valid for a period; `SingleDenotation.current` goes forward (running the next `DenotTransformer`) or back |
| flags at a phase | one raw word through `phase.flagMask`; "late" flags set early become visible from a phase, "anti" flags hide one (`notPRIVATE`): phase-indexed by a static schedule | part of each denotation version |
| name at a phase | `rawname`, **overwritten** by LambdaLift (`renameSym`) and private-name expansion (`expandName`); after flatten, reinterpreted (`needsFlatClasses` → `flattenedName`) | part of each version; LambdaLift, Flatten and ExpandPrivate are symbol transformers |
| owner at a phase | `rawowner`, **overwritten** by LambdaLift (`owner_=`, the old one kept in `originalOwnerMap`); after flatten, reinterpreted | part of each version |
| a flag set by an info transformer | UnCurry's info transformer adds `METHOD` to a nested module **in the raw flags** ([scala/bug#8907](https://github.com/scala/bug/issues/8907)) | in the new version only |

[`phase_ranked`](../../query/Query/Lazy.lean#L199): if no fact reads a later phase, and the reads within a phase are ranked, the whole system is ranked (phase first, lexicographically), so phase-indexed laziness is sound and order-independent. The overwritten facts break the premise in a different way: the store is not indexed by phase, so a typer-phase question's answer depends on whether a later phase has run ([`localName_versioned`](../../scala-types/ScalaTypes/Laziness.lean#L200), [`localName_overwritten`](../../scala-types/ScalaTypes/Laziness.lean#L204)). Measured on the program below with `Phases2`/`Phases3`:

```scala
class A {
  private def secret = 1
  def m(x: Int)(y: Int): Int = { class L { def z = secret }; new L().z + x + y }
  object O
  def g[T](t: T): T = t
}
```

| typer-phase question | asked during the run | asked after the run, scalac 2.12.21 / 2.13.18 | dotc 3.9.0 |
|---|---|---|---|
| `secret.name` | `secret` | `p$A$$secret` | `secret` |
| `L.name`, `L.owner` | `L`, `m` | `L$1`, `A` | `L`, `m` |
| `O.isMethod` | false | true | false |
| `secret.isPrivate` | true | true (anti-flag, phase-indexed) | true |
| `m.info` | `(x: Int)(y: Int): Int` | the same (`TypeHistory`) | the same |

This is also where Track N meets Track L: a binary name ([track-s.md](track-s.md), "Binary names of classes and objects") is the name fact at the last phase, and the lambda-lifted `L$1` that scalac writes into `InnerClasses` is the overwritten name, which dotc keeps as `L`.

## 6. Order sensitivity, measured

A well-founded program compiles the same in every order ([`forceAll_ok`](../../query/Query/Lazy.lean#L160)). [`probes/forcing/order.py`](../probes/forcing/order.py) tests the converse on real compilers, after scala/scala's `DeterminismTester` (`test/junit/scala/tools/nsc`): a reference build of all files in their order; then every permutation of every subset of the files (`permutationsWithSubsets`), the whole set jointly from scratch, a proper subset from source against the reference's classfiles (what an incremental build does after an edit to it); and every order of separate compilation, one file at a time. Each build is compared with the reference, not only accepted or rejected: byte-identical, `members` (a classfile's flags, superclass, interfaces, fields or methods differ), or `tasty` (only TASTy or classfile attributes differ, the pickling artefact of [scala/scala3#26551](https://github.com/scala/scala3/issues/26551)). Four of `DeterminismTest`'s own programs are controls, and give byte-identical output in every order on all three compilers. Of thirty programs (implicit candidates, conversions, overloading, case-class defaults, parents, inherited types; for Scala 3 also exports, givens, extension methods and transparent inline), five are order-sensitive:

* **An implicit candidate skipped while it is completed** (scalac 2.12.21 and 2.13.18):

  ```scala
  // O.scala
  object O { implicit val x: Int = 1; implicit def y = U.z + 1 }
  // U.scala
  object U { import O._; def z = implicitly[Int] }
  ```

  With `O.scala` first, completing `y` types `U.z`, whose implicit search skips `y` (`LOCKED`) and resolves to `x`: it compiles, and `U.z` is `1`. With `U.scala` first: "recursive method z needs result type". Recompiling `U.scala` alone, with `y`'s type from the classfile: "ambiguous implicit values". So **a clean build accepts what an incremental build rejects**: retronym/zinc `claude/order-sensitive-implicit` has it as a pending scripted test, failing on Zinc `develop` after a comment-only edit to `U.scala`. In the model, a consumer that *peeks* ([`Query.Lazy.forcePeek`](../../query/Query/Lazy.lean#L249)) instead of forcing, and the three outcomes by `decide` ([`implicitSkip_O_first`](../../scala-types/ScalaTypes/Laziness.lean#L242), [`implicitSkip_U_first`](../../scala-types/ScalaTypes/Laziness.lean#L247), [`implicitSkip_separate`](../../scala-types/ScalaTypes/Laziness.lean#L252)). The same shape through an implicit conversion behaves the same. Scala 2.13 warns that an implicit definition should have an explicit type; Scala 3 requires one, which removes the shape. Within one file both orders compile: the order that matters here is the order of compilation units.
* **An exported member silently missing** (dotc 3.9.0): `object A { export B.*; def a = 1 }` with `object B { def b = A.a + 1 }`. Typed `A.scala` first, `A` has the forwarder `b`; typed `B.scala` first, it has none, and nothing is reported. The same sources give `A` different public members, so a client calling `A.b` compiles against one build only. `b`'s inferred type completes `A`, whose wildcard export reads `B`'s members while `b` is in progress: the same skip as scalac's implicit search, here silent. A three-object variant behaves the same in two of six orders. Draft report: [`dotc-export-order.md`](../../../docs/upstream/dotc-export-order.md) §1.
* **Mutual wildcard exports** (dotc 3.9.0): `object A { export B.*; def a = 1 }` with `object B { export A.a; def b = 2 }` fails with "Conflicting definitions" typing `A.scala` first and compiles typing `B.scala` first. `A`'s wildcard export reads `B`'s member set while `B`'s own export forwarders are still being added to it: a growing fact read without a freeze, the shape of §4 ([`exportOrder_reads_differ`](../../scala-types/ScalaTypes/Laziness.lean#L275)). Draft report: [`dotc-export-order.md`](../../../docs/upstream/dotc-export-order.md).

dotc's givens and extension methods are order-independent in every shape tried (a given whose definition reads the program that summons it, a given beside an inferred `def`, mutual extensions, an extension overloaded with one being completed): requiring a given's type removes the skipped-candidate shape, and what remains order-sensitive in dotc is a member set that grows (exports). The rest either compile in every mode, are rejected in every mode (some with a diagnostic that depends on the order: overloading across files is "overloaded method f needs result type" one way and "recursive method g needs result type" the other), or are Scala 3 programs skipped for Scala 2.

## Recipes

For someone changing either compiler, the model reduces to a few rules:

* **Ask the narrowest fact.** Inside a completer, ask level 0 and 1 of anything that may be completing: a type constructor, a flag known before completion, a member's symbol rather than its info. A consumer of *every* member's signature (overloading, implicit eligibility, wildcard imports, `export`) inside a completer is a spurious cycle waiting for the right program.
* **Publish early what others will ask for.** Type parameters before bounds (`PolyTypeCompleter`), member names before parents (`TempClassInfo`).
* **Read the past with the right tool.** In scalac, `enteringPhase` is reliable for info and masked flags, not for a name or owner after LambdaLift (use `originalOwner`, or record the name before); in dotc, `atPhase` is reliable for all four.
* **Freeze what you read of a pushed fact**, or complete its producers first.
* **Permute to classify.** If a cycle comes and goes with file order, joint versus separate compilation, or an unrelated edit, it is spurious.

## Evidence

* **Forcing footprints** ([`probes/forcing/Footprint2.scala`](../probes/forcing/Footprint2.scala), [`Footprint3.scala`](../probes/forcing/Footprint3.scala); outputs `footprint-<version>.txt`): symbols whose infos are spy completers, and which of them each operation forces, cold, from inside a member's completer and from inside the class's. scalac 2.12.21 and 2.13.18 give identical tables. The differences from dotc 3.9.0 are the rows of the levels table above, plus: `erasure(A.typeRef)` completes `A` in scalac and nothing in dotc.
* **Phase-indexed facts** ([`probes/forcing/Phases2.scala`](../probes/forcing/Phases2.scala), [`Phases3.scala`](../probes/forcing/Phases3.scala); outputs `phases-<version>.txt`): the table in §5.
* **Order sensitivity** ([`probes/forcing/order.py`](../probes/forcing/order.py), [`order/`](../probes/forcing/order)): §6.
* **The cycle battery** ([`probes/forcing/battery.py`](../probes/forcing/battery.py), [`battery/`](../probes/forcing/battery)): twenty-four programs — case class and companion, inherited result types, F-bounds, annotations, partial information about parents — each with its expected verdict per compiler and its kind. Thirteen are fine everywhere, seven are true cycles everywhere, four are spurious in Scala 2 only (one, a parent's type argument aliased in the companion, already fixed in 2.13), and none is a cycle in dotc that scalac accepts. One spurious program (`class C extends D[C { def x: Int }]`) crashes scalac 2.13.18 with an uncaught `TypeError`.

## Future work

- [x] The order-sensitivity harness (§6), after `DeterminismTester`: thirty multi-file programs, every ordered subset against the reference's classfiles, separate compilation, outputs compared byte by byte and member by member; five order-sensitive.
- [ ] Namer's eager forcings as their own families: case-class synthetics, Scala 3 `export` forwarders, implicit eligibility without a result type, Scala 2 macro annotations.
- [x] A cycle avoided by skipping the fact (scalac's implicit candidates): `forcePeek`, and one program with three outcomes (§6).
- [ ] Zinc: a spurious cycle across files makes an incremental build's verdict depend on which files it recompiles; [phase 15](../../zinc/docs/15-cycles.md) restated over `Query.Lazy`.
- [ ] File the drafts: [`scalac-refinement-parent-crash.md`](../../../docs/upstream/scalac-refinement-parent-crash.md) (the crash, 2.12 and 2.13) and [`dotc-export-order.md`](../../../docs/upstream/dotc-export-order.md).
- [x] Scala 3 givens and extension search across files in the order harness: order-independent in every shape tried.
- [ ] Scala 2 macro annotations in the order harness (they expand in Namer).
