# Track S — the Scala layer (`Scala/`)

## Problem

Each Zinc feature file has its own toy Scala, sized to what Zinc hashes, and none of them says what classfiles scalac actually emits. Binary compatibility (Track B) needs exactly that: a library edit in Scala source, lowered to classfiles, linked by `Jvm`. And three copies of "a member's type as seen from a prefix" (the TCK's, `Zinc/Hier`/`Zinc/Erasure`, and lowering's own substitution) answered one question in three incomparable ways.

## What was built

**Lowering is a `Task`** ([`packages/scala/Scala/Lower.lean`](../Scala/Lower.lean)). Its queries are other definitions' interfaces (`decl d`: kind, parents, members with signatures, no bodies), which is what scalac reads from pickles or TASTy. Lowering a unit asks for its own declaration, its ancestors' (linearization, mixin forwarders, bridges), each value class in a signature (erasure) and its companion (static forwarders). Its output is `ClassOut`: a [`Jvm.Classfile`](../../jvm/Jvm/Link.lean#L115) plus what `Jvm` does not model (fields' flags, `ACC_BRIDGE`, `InnerClasses`, the invokes of synthesized bodies). So lowering has a trace, and `lower_congr` is T1 for it: an edit outside a unit's trace leaves its classfiles unchanged. That is the hook to [`XCompiler`](../../inc-comp/IncComp/General.lean#L22) and Track B4.

**Scala 2.12, 2.13 and 3 are one parameter,** `Dialect`, read only where the probe found the compilers differ.

**Calibration is by probe, not by reading the spec.** A Lean exe enumerates a bounded space, prints each program as Scala source and as the model's classfiles; [`packages/scala/probes/probe.py`](../probes/probe.py) compiles them with each scalac (one run per dialect, two for separate-compilation cases), parses the classfiles and diffs. Enumeration is testing, per [`docs/specification.md`](../../../docs/specification.md).

Steps:
- Track S1: lowering for Scala 2.12+: classes, traits (defaults, `$init$`, static `m$`, trait fields), mixin forwarders, objects (`MODULE$`, static forwarders), bridges, value classes.
- Track S2: Scala 3 deltas: trait initialisers under separate compilation (F6), `@static`, extension methods, `Serializable` objects.
- Track S3: the calibration probe.
- Track S4: one `asSeenFrom`, shared with the TCK ([`packages/scala-types/ScalaTypes/AsSeenFrom.lean`](../../scala-types/ScalaTypes/AsSeenFrom.lean)).
- Track S5: membership and overriding as refchecks ([`packages/scala-types/ScalaTypes/Members.lean`](../../scala-types/ScalaTypes/Members.lean)).
- Track S6: case classes, enums, inline and opaque, nested classes, by desugaring ([`packages/scala-types/ScalaTypes/Desugar.lean`](../../scala-types/ScalaTypes/Desugar.lean)).
- A source-level edit catalogue ([`packages/scala/Scala/Catalogue.lean`](../Scala/Catalogue.lean)), the input to Track B3.

All done.

## Results

### Lowering (Tracks S1–S3)

The probe agrees with scalac on header, fields, methods with flags, `InnerClasses`, and the invokes of synthesized bodies, on every program: 1348/1348 on 2.12.21 and 2.13.18, 1363/1363 on 3.9.0. Families: mixin 1280, generic 24, `asf` 10, value class 4, trait companion 2, `$init$` joint and separate 3+3, misc 4; on Scala 3 also `@static` and extension methods; and the Track S6 families below.

The model started from the textbook rules. The probe corrected it here, each now a rule in `Lower.lean`:
- **Interfaces are minimised.** A direct trait parent that another direct parent already extends is not in the interface list. All three versions.
- **`$init$` is not universal.** Scala 2 omits it for a trait with no concrete member; Scala 3 emits it only for a trait with initialisers.
- **Objects changed in 2.13.** 2.12: instance fields, non-final `MODULE$`, `$init$` calls in the constructor, trait-field implementations `final`. 2.13 and 3: static fields, `final MODULE$`, `$init$` calls in `<clinit>`, trait-field implementations not final.
- **Static forwarders include inherited members.**
- **Scala 3 forwards more:** trait setters, and a bridge when the first member of that erased signature along the linearization is concrete.
- **Scala 3 objects** are `Serializable` with a private `writeReplace`; an object implementing a `lazy val` has a private `<clinit>`.
- **Trait setter names carry the trait's full name,** package mangled: `p1$T$_setter_$v_$eq`.
- A mixin forwarder for a `final` trait method is `final`. A Scala 3 `@static val` is a public static final field of the companion class, with no accessor.

**F6, extended.** A Scala 3 trait whose only initialiser is a `lazy val`, *or which has any extension method*, has an `$init$`. A subclass compiled in the same run calls it; one compiled against the trait's TASTy does not (the TASTy says `NoInits`). The extension-method case is new and likely the common one (syntax traits for type classes). In the model lowering depends on `View.inRun`, a compositionality failure witnessed by kernel `decide` in [`packages/scala/Scala/Facts.lean`](../Scala/Facts.lean) (`ctorInits`); the probe confirms both runs. Track B4 shows what it costs and that [retronym/scala3#10](https://github.com/retronym/scala3/issues/10) fixes it.

### One `asSeenFrom` (Track S4)

[`packages/scala-types/ScalaTypes/AsSeenFrom.lean`](../../scala-types/ScalaTypes/AsSeenFrom.lean) defines scalac's `asSeenFrom(pre, clazz)` once, generic in the type language: any language with substitutable leaves (this-types and class type parameters, anchored at their owner) and a lawful `bind`. `leafAsSeen` is the walk; `asf` is `bind` of it. `compose` and `chain_is_single` are proved once, from lockstep. It imports only Lean core, so a Mathlib-free project can use it.

Consumers:
- **Lowering.** `lin` computes each base type's arguments as `asSeenFrom(C.this, P)` (scalac's `baseType`), replacing an ad hoc substitution; members are grouped by `memberType` (`sigGroups`), and bridges and forwarders work per group. The new `asf` probe family found two corrections: a bridge to an override at a value class unboxes and boxes, and an overload next to an inherited generic method is not an override (name-only lookup had dropped a mixin forwarder).
- **The TCK.** On retronym/scala-type-system-tck branch `claude/shared-asf`, `lean/AsSeenFrom/Shared.lean` is a vendored copy, and [`Port.lean`](../../intellij/IntelliJ/Port.lean) makes the TCK's `Ty` an instance and proves its [`Scalac.asf`](../../intellij/IntelliJ/Scalac.lean#L34) *is* the shared map ([`asf_eq`](../../intellij/IntelliJ/Port.lean#L85) in that file). [`Chain.compose`](../../intellij/IntelliJ/Chain.lean#L82) now follows from the shared `compose`; the other TCK results build unchanged.
- **`Zinc/Hier`:** its member lookup is [`Scala.lookupH`](../../scala-types/ScalaTypes/Resolve.lean#L216), the shared walk over `header` and `member` queries, proved equal to lookup over declarations ([`Scala.lookupH_eq`](../../scala-types/ScalaTypes/Fine.lean#L240)); `HierShared.toy_eq_shared` for every `Hier` program. **`Zinc/Erasure`, `Flat`, `ImplicitScope`:** not yet; see [`packages/zinc/docs/29-shared-scala.md`](../../zinc/docs/29-shared-scala.md).

### Membership and overriding (Track S5)

[`packages/scala-types/ScalaTypes/Members.lean`](../../scala-types/ScalaTypes/Members.lean) is refchecks as a `Task` over interfaces, on the shared `asSeenFrom`: for a class, either the errors scalac or dotc reports, or per signature the member a selection runs. Calibrated by [`packages/scala/probes/members.py`](../probes/members.py) on 4704 hierarchies (`T`, `U`, `B`, `C`, each declaring `m` one of eleven ways), **rejected programs included**: errors are compared per class and kind, and for accepted programs a `main` checks which owner's `m` runs.

| compiler | agree | accepted |
|---|---|---|
| 2.12.21 | 4700/4704 | 772 |
| 2.13.18 | 4700/4704 | 772 |
| 3.9.0 | 4704/4704 | 672 |

The rules the probe forced, beyond the textbook:
- **One error per position,** in the order access, `final`, missing `override`, accidental override, `def` over `val`, lazy against strict, result type; errors of inherited pairs and abstract members are at the class, where only the first is printed.
- **Which pairs.** A pair a parent has is left there by 2.12; **2.13 checks it again** in each subclass, and dotc does when the parent has the two owners in the other order ([scala/bug#11136](https://github.com/scala/bug/issues/11136), `recheck11136`).
- **Private.** A private member isn't inherited and implements nothing. Scala 2 stops at it; Scala 3 also checks the inherited member it fails to hide. `override private` is a refchecks error in Scala 2 and an earlier-phase error in Scala 3; each program now compiles on its own in the compile server, so it hides nothing else.
- **Accidental override needs a real override;** otherwise it is "inherits conflicting members".
- **Re-abstraction.** An abstract member of a *class* re-abstracts the concrete one it extends; one in a *trait* does not. Scala 3 forms a pair there; Scala 2 doesn't.

**A scalac 2 bug, found by the runtime check** (the 4 disagreements). `trait T { val m = "T" }; abstract class B extends T { def m: String }; class C extends B with T { override val m = "C" }` compiles with 2.12.21 and 2.13.18, and `new C` throws `AbstractMethodError`: `T.$init$` calls the trait setter, which `C` does not implement. Scala 3 (3.3.7, 3.9.0) rejects `B` instead: "method m of type => String needs to be a stable, immutable value". Filed as [scala/bug#13199](https://github.com/scala/bug/issues/13199), with the cause (the Fields phase drops the trait setter, and refchecks never checks the re-abstracting pair) and the draft fix [retronym/scala#136](https://github.com/retronym/scala/issues/136). The nearest earlier report, [scala/bug#12456](https://github.com/scala/bug/issues/12456), is a different shape (a Java abstract class between the trait and the class).

**Java's rules (JLS 8.4.8), the spec Track V diffs against:**
- **Order.** No linearization: a class method always beats an interface default; among interfaces the maximally specific default wins, and two unrelated defaults are an error unless the class declares the method.
- **Same member** by subsignature (a raw method overrides a generic one); same erasure without override is a clash. Scala matches by `memberType` and uses erasure only for bridges.
- **No `override` keyword**, so no "needs `override`", "conflicting members" or third-member rule.
- **Access and statics.** A package-private method is not overridden from another package, and the JVM's selection agrees (Track J3). Statics hide, they don't override.
- **Re-abstraction** is allowed in both; Java also checks `throws`.


**Two gaps found from `Flat` (12 October).** Comparing `Flat`'s refchecks with `Members` over `FlatRules`' 216,000 programs ([`packages/zinc/Zinc/Bridges/FlatShared.lean`](../../zinc/Zinc/Bridges/FlatShared.lean)) showed shapes the calibration space never reached, since all its members have result type `String` and `T` is always mixed into `C` directly. Checked one by one against scalac 2.13.18 and dotc 3.9.0, both now in `Members`, each pinned by a witness (`implIncompatible`, `reabsTraitOnly`, `reabsTraitDirect`, `reabsAbstractClass`, `reabsClassDirect`, `reabsTraitViaClass`):

- An abstract member and a concrete one of an incompatible type, through different parents (`class C extends B with M`, `B.m: String`, abstract `M.m: Int`): both compilers reject `C` ("incompatible type"). `Members` had skipped every abstract/concrete pair.
- Re-abstraction. Both compilers let a class's abstract declaration re-abstract an inherited concrete member, even when the class also mixes the concrete trait in directly. A trait's does so only in Scala 3, and only when no direct parent supplies the concrete member (`concreteS3`). The specification says neither: a concrete definition always overrides an abstract one (SLS §5.1.4). javac always lets the abstract redeclaration win (JLS §9.4.1, §8.4.8), as JVM selection does; Scala 2.13 follows the specification for traits and emits a mixin forwarder.

The calibration is unchanged with the fixes: 4,700/4,704 on 2.12.21 and 2.13.18, 4,704/4,704 on 3.9.0.

### Case classes, enums, inline and opaque, nested classes (Track S6)

**Desugaring plus a library prelude, not new lowering rules.** Each feature is a desugaring into the existing AST. What the compiler inherits from the library (`Product`, `Equals`, `AbstractFunctionN`, `Mirror`, `scala.reflect.Enum`) enters as declarations in a prelude, read through `Q.decl` like any parent. The calibrated forwarder and bridge rules do the rest, so the probe tests the desugaring and the prelude together.

| family | 2.12.21 | 2.13.18 | 3.9.0 |
|---|---|---|---|
| `case` | 14/14 | 14/14 | 14/14 |
| `nest` | 3/3 | 3/3 | 3/3 |
| `sealed` | 1/1 | 1/1 | 1/1 |
| `enum` | | | 4/4 |
| `inline` (and opaque) | | | 5/5 |

What the probe corrected:
- **Case classes.** Synthesized `copy`, `toString`, `hashCode`, `equals`, `canEqual` are skipped when a *superclass* defines one concretely (a trait's doesn't count); `productPrefix` is always synthesized. With a superclass's `copy`, Scala 3 keeps `copy$default$N`, Scala 2 drops it. Only a synthesized companion extends `AbstractFunctionN` and overrides `toString`. Serializable objects get `readResolve` in 2.12, `writeReplace` in 2.13; Scala 3 makes every object `Serializable`.
- **Nesting.** A nested object gets no mirror class; its module class has a public constructor, final only in Scala 3, where the enclosing module class also gets a static field for it. `InnerClasses` names the mirror or companion as outer; a nested class and its companion list each other.
- **Enums.** `values`, `valueOf`, `$values` exist only when every case is a singleton; `$new` is private with no static forwarder.
- **Inline.** An `inline def` is in the classfile only when it implements or overrides a member.

### The source-level catalogue

[`packages/scala/Scala/Catalogue.lean`](../Scala/Catalogue.lean): library edits in Scala source, each lowered and linked `before`, `after` (old client classfiles, new library) and `fresh` (client recompiled) by kernel `decide`. Two show the gaps between Zinc and binary compatibility:
- `traitOverrideAdded`: the old client has no forwarder, so the JVM selects the superclass's method; a fresh build runs the trait's. Links either way, MiMa is silent, Zinc must recompile. Confirmed on HotSpot with 2.13.18.
- `widenedToValueClass`: `W`'s classfile changes although `W`'s source did not, because its lowering trace contains `V`.

And from Track S6: `caseFieldAdded` (accessor links; constructor, `apply`, `copy` don't), `nestedClassMoved` (`NoClassDefFoundError`), `enumCaseAdded` (links), `enumCaseRemoved` (`NoSuchFieldError`), and `inlineBodyChanged`: the library's classfiles are *equal* before and after while every client holds the old body. Binary compatibility can't see it; Phase 11's `InlineOpaqueSpec` gives Zinc the keys for it.

**Synthesized bodies run (Track J4).** `ClassOut.toJvm` keeps the invokes of synthesized bodies as the methods' bodies: a mixin forwarder runs `T.m$`, which runs `T.m`; a constructor runs its traits' `$init$`, which now carries the setter calls of the trait's `val`s (calibrated: 1,929 `$init$` bodies agree with scalac 2.12, 2.13 and 3 in the space above); a static forwarder reads `MODULE$` and calls the module. A new instance runs its `()V` constructor's body. So `valAddedToTrait` fails at `new X`, as on HotSpot: `X.<init>` runs `T.$init$`, which calls the setter the old `X` lacks. The outcomes now list the methods each site enters.

**At scale: `FlatRules`' programs (13 October).** `lake exe scalaprobe OUT flat` prints `FlatRules`' 216,000 configurations through `FlatShared`'s embedding: 48,000 distinct programs for the 192,000 without a `var` (bodies, which the embedding drops, are what tell the rest apart); the 24,000 with a `var` are `FlatShared`'s known exclusion. [`members.py OUT --space flat --pool 4`](../probes/members.py) compiles each on its own and runs the accepted ones. The first run agreed on about 10,500 programs per compiler; every disagreement shape was a `Members` gap, fixed from the compilers' sources, none a compiler bug or a known `FlatShared` exclusion:

| shape | fix in `Members` |
|---|---|
| a `final` parent; two instances of `M` (`A extends M[String]`, `C … with M[Int]`): typer errors, which stop refchecks | `typerDecl`, `reported` |
| which of a class's errors is printed | the compilers' `OverridingPairs.Cursor` order (`pairs2`), one error per position |
| `object X extends C`, `C` concrete and re-abstracting: no error in `X` | re-abstraction only through abstract superclasses (`missingS2`) |
| dotc: "not a legal implementation" in `C` for a pair `B` already rejected | `checkMemberTypesOK` |
| dotc: a trait's private `val` counted as implementing | `concreteS3` skips private members |

| date | commit | space | compiler | programs | agree | wall (K=4) |
|---|---|---|---|---|---|---|
| 13 Oct | 7a9e2a0 | FlatRules | 2.12.21 | 48,000 (192,000 configurations) | 48,000 | 34 s |
| 13 Oct | 7a9e2a0 | FlatRules | 2.13.18 | 48,000 | 48,000 | 36 s (64 s at K=1) |
| 13 Oct | 7a9e2a0 | FlatRules | 3.9.0 | 48,000 | 48,000 | 53 s |
| 13 Oct | 7a9e2a0 | members | 2.12.21, 2.13.18, 3.9.0 | 4,704 | 4,700, 4,700, 4,704 | 14–17 s |

**Against the specification.** Each rule above was taken from a compiler's source, so each was checked against SLS §5.1.3–5.1.4 rather than accepted. The specification says which member overrides which and what an override must satisfy, not which errors are printed. Over both spaces, scalac 2.12 and 2.13 accept the same programs; dotc rejects 124 that they accept, in two families, both an abstract declaration meeting a concrete member, which §5.1.3 says the concrete one overrides: a trait's re-abstraction (`reabsTraitOnly`, 24 programs), and dotc checking the abstract declaration as an override of the concrete one (`abstractOverFinal` for `final`, and stability; 108), 8 programs in both. scalac follows the text in both; both are in [`docs/upstream/spec-reabstraction.md`](../../../docs/upstream/spec-reabstraction.md), with the `final` case new. Every other compiler-specific rule (the cursor's order, the first error per position, the abstract-superclass chain, dotc's private split and member-type re-check) only moves errors between the classes of a program that is rejected anyway; the member a call runs agrees across all three compilers on every accepted program. 2.12's leaving a pair to a parent is unsound, and fixed in 2.13 ([`mixin-final-override-recheck.md`](../../../docs/upstream/mixin-final-override-recheck.md)).

**The catalogue on HotSpot.** [`packages/scala/probes/run.py`](../probes/run.py) compiles each case with scalac 2.13.18 in the compile server (`v0`, the client against `v0`, `v1`), instruments the classfiles to log each method entered ([`Instrument.java`](../../jvm/probes/Instrument.java)), and runs the sites through [`packages/jvm/probes`](../../jvm/probes) on HotSpot 21, 25 and 27. The 9 cases that compile with Scala 2 agree on every `Throwable` and on the sequence of methods entered, with one exception: `caseFieldAdded` on `v0`, where HotSpot also enters `P.<init>` from `copy` and from the companion's `apply`. Those bodies come from the case-class desugaring as user members, which lowering does not synthesize; the linkage outcome agrees. Class initialisation is not modelled, so the probe mutes static initialisers, as it mutes building a receiver.

### Refchecks accepted, so no `AbstractMethodError` (Question 1)

A static promise across three layers ([`packages/scala/Scala/Refchecks.lean`](../Scala/Refchecks.lean), `lake build Scala.Refchecks`, about 20 minutes). Over the 4,704 programs of [`Members.membersSpace`](../../scala-types/ScalaTypes/Members.lean#L532) and each of scalac 2.12.21, 2.13.18 and dotc 3.9.0, [`refchecks_sound`](../Scala/Refchecks.lean#L275) decides by the kernel, in chunks of 400 programs:

- `Members` (typer's inheritance checks and refchecks, `reported`) accepts exactly the programs the compiler accepts (772, 772 and 672);
- for an accepted program and each concrete class `C` whose `m` `Members` says comes from owner `O`, HotSpot ran `O`'s `m` (the oracle is `members.py`'s run of `new C().m` on each accepted program, written by [`members_lean.py`](../probes/members_lean.py) into `RefchecksData`, as Track T's `PathsOracle` does);
- the program lowered by [`Scala.lowerProgram`](../Scala/Lower.lean#L551) and linked by `Jvm` (constructor and `$init$` bodies run) enters `O`'s lowered method last, directly or through `C`'s mixin forwarder and `O.m$`, or, for a trait's `val`, the class's accessor; so it links, and throws no `AbstractMethodError`.

The exclusions are named:

- **`bug13199`**, four programs, Scala 2 only: a class's abstract `def m` re-abstracts a trait's `val m` and the subclass overrides it with a `val`. 2.12 and 2.13 accept them, and HotSpot throws `AbstractMethodError` ([scala/bug#13199](https://github.com/scala/bug/issues/13199)); dotc rejects them ([`bug13199_witnesses`](../Scala/Refchecks.lean#L285)). These are the only accepted programs of the space that fail at run time, under any of the three compilers.
- **`lowerGap`**, from the model's side only: the rows `Scala.Lower` does not model. A trait's `val` overridden by the class: scalac and dotc still give the class the trait's setter `T$_setter_$m_$eq`, which `$init$` calls, and lowering does not, so the model's `new C` fails where HotSpot runs (20 class/owner pairs per Scala 2 dialect, 15 for Scala 3); and a trait's `lazy val`, whose implementation in a class lowering only partly models (24 and 16). Widening `Lower` for them is open; the `bug13199` programs are in the first row.

## Out of scope

Method bodies and call sites in user code; overloading in general; generic `Signature` attributes; `lazy val` and `var` implementation in classes; `private[this]` and qualified access; specialization; Java-defined parents; given instances; case classes with type parameters, several parameter lists or private constructors; enums with type parameters; local classes; macros. The open items are in [`docs/roadmap.md`](../../../docs/roadmap.md).

## PRs

- [retronym/talks#39](https://github.com/retronym/talks/issues/39): lowering, calibration against 2.12/2.13/3 (Tracks S1–S3) and the catalogue.
- [retronym/talks#56](https://github.com/retronym/talks/issues/56): the shared `asSeenFrom` (Track S4).
- [retronym/talks#58](https://github.com/retronym/talks/issues/58): membership and overriding (Track S5).
- [retronym/talks#65](https://github.com/retronym/talks/issues/65): case classes, enums, inline and opaque, nested classes (Track S6).
