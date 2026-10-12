# Track T: type soundness by oracle

Design, 13 October 2026. Question 8 of [`docs/history/reviews/2026-10-12-specifications.md`](../../../docs/history/reviews/2026-10-12-specifications.md).

## Why

Soundness, as the review frames it, is a static promise kept by the dynamic semantics. For types the promise is the oldest one: a program the compiler accepts does not go wrong. On the JVM, "goes wrong" has a precise witness. Erasure inserts a `checkcast` wherever a value whose static type was erased flows into a position that needs its class, so a value of the wrong class reaching such a position throws `ClassCastException`. A `ClassCastException` in a program whose source contains no cast (no `asInstanceOf`, no type test or type pattern) is the type checker's promise broken.

The DOT line of work proves a core calculus sound. The question for an implementation is the gap between that calculus and what scalac and dotc accept, and that gap is concrete and partly known. Amin and Tate turned two Scala compilers' acceptance of a `null` path with conflicting bounds into a function of type `T => U` with no cast. Dotty's realizability check was built to close the same hole for `lazy val` paths and projections, and leaves `null` open by its own account.

This repository's method fits the gap and not the theory: enumerate small programs over the shapes that matter, ask each compiler whether it accepts each one, run the accepted ones, and compare. The compile server ([`packages/harness/docs/compile-server.md`](../../harness/docs/compile-server.md)) makes that cheap: 3 to 15 ms per compile and about 10 ms per run on a warm JVM, for scalac 2.12.21, 2.13.18 and dotc 3.9.0.

**What this track is not.** It is not a soundness proof of Scala, of DOT, or of a fragment. That problem has absorbed a succession of theses (DOT, pDOT, the undecidability of D<:) and is out of scope. The Lean side models *the compilers' checks* on bounded spaces, calibrated against the compilers, and states theorems only of this shape:

> for every program `p` of space `S` other than the named exceptions, if the model of compiler `c`'s check accepts `p`, then the oracle's run of `p` has no cast-free `ClassCastException`.

Such a theorem is decided by the kernel over `S`, with the oracle's verdicts as data, as the calibration tables are elsewhere. A counterexample is never explained away: it is named in the theorem's exclusion list, with its source, and reported.

## The oracle

A program is compiled by each compiler through the server. If it is accepted, it is run once through the server's `run` op on HotSpot. Its verdict is one of:

| verdict | meaning |
|---|---|
| `rejected e` | the compiler reports error `e` (kind and message, as in the calibration probes) |
| `ok` | runs to completion |
| `cce` | a `ClassCastException`, and the source has no cast: an unsoundness |
| `expected t` | a throwable the program provokes on purpose: `NotImplementedError` from `???`, a `NullPointerException` from dereferencing a `null` path |
| `other t` | anything else (`AbstractMethodError`, `NoSuchMethodError`, a `StackOverflowError`): reported, and treated as a finding until classified |

"Cast-free" is a property of the generated source, not of a scan: the generator never emits `asInstanceOf`, `isInstanceOf`, a type pattern or a type ascription to a non-supertype, so every `ClassCastException` in an accepted program is a checker failure by construction. Pattern matching is left out of the first space for that reason ([scala/scala3#16728](https://github.com/scala/scala3/issues/16728) is a projection-pattern soundness bug of a different kind).

## Prior art

- **Amin and Tate**, *Java and Scala's Type Systems are Unsound: The Existential Crisis of Null Pointers*, OOPSLA 2016 ([paper](https://infoscience.epfl.ch/record/227019), [artifact](https://github.com/namin/unsound)). The Scala program: `trait LowerBound[T] { type M >: T }`, `trait UpperBound[U] { type M <: U }`, a local `val bounded: LowerBound[T] with UpperBound[U] = null`, and a dependent method `upcast(ub: LowerBound[T], t: T): ub.M = t`. `coerce[Integer, String](0)` throws a `ClassCastException`. The artifact's `legacy.scala` gets the same effect without dependent method types, through a `final val ub: X = compute` field whose `compute` returns `null`. The paper's point is that `null` inhabits every type, including one whose bounds are contradictory. A type checker that relies on "a path's type is inhabited, so its bounds are consistent" is unsound as soon as `null` is a path.
- **[scala/bug#9633](https://github.com/scala/bug/issues/9633)**, *soundness issue with path-dependent type on `null` path* ([issue](https://github.com/scala/bug/issues/9633)): the same hole as a Scala 2 report, with `trait A { type L <: Nothing }`, `trait B { type L >: Any }` and `val p: B with A = null`. It is open with the label "should not compile"; in 2023 it was noted as still compiling with Scala 3.3.0-RC6.
- **[scala/scala3#50](https://github.com/scala/scala3/issues/50)**, *isVolatile incorrect for intersection types* ([issue](https://github.com/scala/scala3/issues/50)): `lazy val o: A & B = ???` with `type X = String` in `A` and `type X = Int` in `B` turns an `Int` into a `String`. It was closed in February 2016 by making realizability consider type aliases. The thread records that a field path is checked only "under strict mode, since fields may be null", and that fixing `null` paths was deferred until non-nullable types exist.
- **[scala/scala3#1050](https://github.com/scala/scala3/issues/1050)**, *Type projection is unsound* ([issue](https://github.com/scala/scala3/issues/1050)): `type X = C { type A >: Any } & C { type A <: Nothing }`, `val y: X#A = 1; val z: String = y`. It was closed by [scala/scala3#1051](https://github.com/scala/scala3/issues/1051). Scala 3 then dropped projection on abstract types ([reference: dropped general type projection](https://docs.scala-lang.org/scala3/reference/dropped-features/type-projection.html)): `T#A` is legal only for a concrete `T`.
- **Odersky, *Scaling DOT to Scala: soundness*** (Scala blog, 17 February 2016, [post](https://www.scala-lang.org/blog/2016/02/17/scaling-dot-soundness.html)): bad bounds cannot be ruled out by a local check, so DOT requires every path prefix to be a value built by `new`, whose bounds were checked at the `new`. Scala departs from this with `lazy val`, `null` and fields, and the realizability check patches the first.
- **DOT and pDOT.** Amin, Grütter, Odersky, Rompf and Stucki, *The Essence of Dependent Object Types* (WadlerFest 2016); Rompf and Amin, *Type Soundness for Dependent Object Types* (OOPSLA 2016); Rapoport and Lhoták, *A Path to DOT: Formalizing Fully Path-Dependent Types* (pDOT, OOPSLA 2019). These calculi are sound because every path is a value; this track measures where the compilers relax that.
- **Explicit nulls.** Nieto, Zhao, Lhoták, Chang and Pu, *Scala with Explicit Nulls* (ECOOP 2020), and dotc's `-Yexplicit-nulls`: with `null` outside reference types, `val p: A & B = null` no longer types. This is the static fix the track can check as a fourth "compiler".
- **dotc's checks.** `CheckRealizable` (`compiler/src/dotty/tools/dotc/core/CheckRealizable.scala`) computes a path's realizability:
  - A stable, non-lazy val is realizable "because we know that a value of type `tp` has been created at run-time".
  - A `lazy val`, or an overridable member, is realizable only if its type is concrete with consistent bounds (`HasProblemBounds`, `HasProblemBase`, `HasProblemBaseArg`).
  - A field's own type is checked only from `-source future`, because "an embedded field could well be nullable".
  - `Checking.checkRealizable` reports from `PostTyper`, as an error or, under `-source 3.0-migration`, a warning.
  - `Checking.checkRealizableBounds` rejects `new C` when `C` has a member with conflicting bounds ("cannot be instantiated since it has a member … with possibly conflicting bounds").
- **scalac's checks.** Volatile types (SLS §3.6). `Typers` rejects a type selection from a volatile type, and abstraction over one (`TypeSelectionFromVolatileTypeError`, `AbstractionFromVolatileTypeError`, `InferTypeWithVolatileTypeSelectionError`). `RefChecks` rejects a volatile member overriding a non-volatile one. Volatility is scalac's approximation of "might have bad bounds", and `null` is outside it.
- **Bonsai** (Scala Symposium 2016, *Automatically finding Scala soundness bugs*) rediscovered [scala/bug#9633](https://github.com/scala/bug/issues/9633) by generating programs. It is the closest prior art for enumeration; this track differs in deciding the compilers' checks in a model and stating the result as a theorem over the space.

## What the type language needs

`ScalaTypes` today has class members with signatures, one level of class type parameters, `Ty.tp`, `Ty.this`, `Ty.ref`, `Ty.inter` of two named definitions (Phase 29), and `asSeenFrom`. For the shapes above it lacks:

| feature | needed for | first space |
|---|---|---|
| abstract type members with bounds (`type L >: lo <: hi`) and aliases (`type L = T`) | all of them | yes |
| path-dependent types `p.L` on a stable path `p` (a `val`, a `lazy val`, a parameter, `this`), and dependent method types (`def f(b: B)(x: …): b.L`) | the Amin–Tate and #9633 programs | yes |
| `null` as a term, and `???` | the path's value | yes |
| intersections whose components carry type members (`A & B`, `A with B`), and refinements `C { type L <: hi }` | bounds that conflict only in combination | yes: the existing `inter`, extended to refinements |
| type projection `T#L` | [scala/scala3#1050](https://github.com/scala/scala3/issues/1050), Scala 2 programs | second space |
| class type parameters in bounds (`LowerBound[T]`) | the paper's generic `coerce` | second space: the first uses concrete bounds (`Int`, `String`), which give the same `ClassCastException` without polymorphism |
| fields of objects as paths, overriding of type members | `legacy.scala`, [scala/scala3#50](https://github.com/scala/scala3/issues/50) under `-source future` | second space |
| pattern matching, variance, higher kinds, recursive types | no first-catalogue case | no |

Terms are minimal: the generator emits a fixed program skeleton (traits, one path definition, one dependent method, a `main` that pushes a value of one type through the path and uses it at another), so the model needs no term typer. Its static side is the checks: well-formed bounds at declarations, realizability of the path (dotc), volatility (scalac), and the subtyping the dependent method's body needs (`x: lo` conforms to `b.L` through `lo <: b.L`).

## The first space

Programs of this skeleton, in a unique package each:

```scala
trait A { type L >: lo_A <: hi_A }      // each bound optional
trait B { type L >: lo_B <: hi_B }
// the path p, of type A with B (Scala 2), A & B (Scala 3), or a refinement of one trait
<path>
def up(b: <B or A or both>)(x: <lo>): b.L = x
def main(...) = { val s: <hi> = up(p)(<value of lo>); <use s as hi> }
```

Factors and levels:

- **Bounds:** `lo_A`, `hi_A`, `lo_B`, `hi_B` each absent or one of `Int` and `String`, with `Nothing`/`Any` as the defaults. These are the bound pairs the catalogue uses, about 9 consistent and conflicting combinations per trait after symmetry.
- **The path:**
  - `val p = null`, `val p = ???`, `lazy val p = ???`;
  - a method parameter `p` passed `null`;
  - `final val p` as a field of an object initialised to `null`;
  - `val p = new A with B {}`, which dotc should reject by `checkRealizableBounds` when the bounds conflict.
- **How `L` is seen:** through `A`, through `B`, or through the intersection.
- **Compiler and options:** scalac 2.12.21; 2.13.18; dotc 3.9.0; dotc 3.9.0 with `-source future`; dotc 3.9.0 with `-Yexplicit-nulls`.

That is about 9 × 9 bound pairs × 6 paths × 3 views ≈ 1,500 programs before pruning the ones that cannot conflict, times five compiler settings: about 7,500 compiles and, at the rates measured for the membership space, under five minutes per setting with the runs. "A few thousand" programs, as planned.

Expected, from the catalogue (to be confirmed in step 2, not assumed):

- every compiler accepts the `null` local and parameter paths and they throw;
- dotc rejects the `lazy val` path ([scala/scala3#50](https://github.com/scala/scala3/issues/50)) and the conflicting `new`;
- the field path is accepted by dotc unless `-source future`;
- `-Yexplicit-nulls` rejects the `null` paths.

## Key decisions

1. **The oracle decides soundness; the model decides acceptance.** Lean never evaluates a program's run. The model encodes each compiler's static check as a `Task` over the shared queries (`header`, and type-member bounds), is calibrated against the compilers' accept/reject verdicts the way `Members` is, and the theorem relates its verdict to the oracle's recorded runs.
2. **Counterexamples are data, named.** The theorem for each compiler setting excludes the programs the oracle saw throw, by name, so its statement *is* the list of unsound programs the compiler accepts. An empty list for `-Yexplicit-nulls`, for example, is the claim worth stating.
3. **Extend `ScalaTypes` minimally, for the first space only.** Type members with bounds, stable paths and `null` go into the shared syntax (step 3), as `Long` and intersections did in Phase 29. Projections, class parameters in bounds, and type-member overriding wait for a second space.
4. **No proof of the general property.** If a step needs the general theory to answer a question (whether a check is complete, whether a bound is ever realizable), the track stops and reports the question.

## Steps

1. This design. **(DONE)**
2. **(DONE, below)** **The catalogue**, before any Lean. The Amin–Tate programs (`unsound.scala`, `legacy.scala`), [scala/bug#9633](https://github.com/scala/bug/issues/9633)'s programs, [scala/scala3#50](https://github.com/scala/scala3/issues/50) and #1050 with their Scala 3 forms, and the dotc test cases of the realizability fixes, as Scala sources in [`packages/scala/probes/soundness/`](../../scala/probes/soundness). Each is compiled with 2.12.21, 2.13.18 and 3.9.0 (plus `-source future` and `-Yexplicit-nulls`) through the server and run where accepted. The result is a table per compiler: rejected (which error), accepted and runs, accepted and throws. That table is a finding on its own, and the first entry of a ledger like the JVM probe's.
3. **The space.** Extend `ScalaTypes` as above; encode dotc's realizability and bounds checks and scalac's volatility as `Task`s; generate the first space (a `lake exe` in the harness, the only harness change), calibrate the model's verdicts against the compilers, run the accepted programs, and state the per-compiler theorems. Every accepted program that throws a cast-free `ClassCastException` is reported with its source.

## Step 2: the catalogue

The known cases are Scala sources in [`packages/scala/probes/soundness/`](../../scala/probes/soundness). They are written once, with `AND` for the intersection operator; the driver writes `with` for Scala 2 and `&` for Scala 3. [`soundness.py`](../../scala/probes/soundness.py) compiles each with the five settings through the compile server and runs `Main` where accepted, in about 15 seconds for all 90. The ledger is [`catalogue.jsonl`](../../scala/probes/soundness/catalogue.jsonl) (13 October 2026, JDK 21).

The cases:

- `at_unsound`, `at_legacy`: the Amin–Tate artifact.
- `bug9633_nothing`, `bug9633_cast`: [scala/bug#9633](https://github.com/scala/bug/issues/9633).
- `s3_50_lazy`: [scala/scala3#50](https://github.com/scala/scala3/issues/50).
- `s3_50_null` and `s3_50_bounds_lazy`: #50 with a strict `null` val, and with bounds instead of aliases.
- `s3_1050_proj`: [scala/scala3#1050](https://github.com/scala/scala3/issues/1050).
- `param_null`, `field_null`, `new_conflict`: one path seen through the intersection (a parameter, a field, a `new`).
- `views_val`, `views_lazy`, `views_param`, `views_field`, `views_new`: the same path seen through each trait separately, `up(a: A)(x: Int): a.L` then `down(b: B)(l: b.L): String`.
- `ok_consistent`, `views_ok`: controls with consistent bounds.

| case | 2.12.21 | 2.13.18 | 3.9.0 | 3.9.0 -source future | 3.9.0 -Yexplicit-nulls |
|---|---|---|---|---|---|
| `at_legacy` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `at_unsound` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `bug9633_cast` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `bug9633_nothing` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `field_null` | rejected: type mismatch | rejected: type mismatch | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `new_conflict` | rejected: type mismatch | rejected: type mismatch | rejected: conflicting bounds | rejected: conflicting bounds | rejected: conflicting bounds |
| `ok_consistent` | rejected: type mismatch | rejected: type mismatch | ok | ok | rejected: `Null` not a subtype |
| `param_null` | rejected: type mismatch | rejected: type mismatch | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `s3_1050_proj` | rejected: type mismatch | rejected: type mismatch | rejected: not a legal path | rejected: not a legal path | rejected: not a legal path |
| `s3_50_bounds_lazy` | rejected: type mismatch | rejected: type mismatch | rejected: not a legal path | rejected: not a legal path | rejected: not a legal path |
| `s3_50_lazy` | rejected: type mismatch | rejected: type mismatch | rejected: not a legal path | rejected: not a legal path | rejected: not a legal path |
| `s3_50_null` | rejected: type mismatch | rejected: type mismatch | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `views_field` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `views_lazy` | throws NotImplementedError | throws NotImplementedError | throws NotImplementedError | throws NotImplementedError | throws NotImplementedError |
| `views_new` | rejected: incompatible override | rejected: incompatible override | rejected: conflicting bounds | rejected: conflicting bounds | rejected: conflicting bounds |
| `views_ok` | ok | ok | ok | ok | rejected: `Null` not a subtype |
| `views_param` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |
| `views_val` | **throws CCE** | **throws CCE** | **throws CCE** | **throws CCE** | rejected: `Null` not a subtype |

Out of 18 programs, 10 are accepted and throw a cast-free `ClassCastException` under 3.9.0, and the same 10 under `-source future`. Under 2.12.21 and 2.13.18 the count is 7, and under `-Yexplicit-nulls` it is none.

Against the predictions of the first space:

- **"Every compiler accepts the `null` local and parameter paths, and they throw."** This holds for 3.9.0. For Scala 2 it holds only when the path is seen through each trait separately (`at_unsound`, `bug9633_*`, `views_val`, `views_param`, `views_field`).
  - *Difference:* scalac rejects every program that sees `L` through the intersection itself, even the consistent control `ok_consistent`, with a type mismatch. A member of `A with B` in Scala 2 is the last parent's (`B`'s `L <: String`, lower bound `Nothing`); its bounds are not the intersection of the parents'. That is scalac's member semantics, not a soundness check: the same bounds are unsound through two views.
- **"dotc rejects the `lazy val` path ([scala/scala3#50](https://github.com/scala/scala3/issues/50)) and the conflicting `new`."** Both hold: "not a legal path" for `s3_50_lazy` and `s3_50_bounds_lazy`, and "cannot be instantiated since it has a member L with possibly conflicting bounds" for `new_conflict` and `views_new`. scalac rejects the conflicting `new` too, in `RefChecks`' override check ("incompatible type in overriding").
  - *Difference:* dotc and scalac accept `views_lazy`. The lazy path is passed as an argument, which forces it, so the program throws `NotImplementedError` before any cast. That is not an unsoundness.
- **"The field path is accepted by dotc unless `-source future`."** *Wrong:* `-source future` accepts `field_null` and `views_field`, and both throw. `CheckRealizable` examines the fields of a path's underlying type only when the path itself needs checking (a `lazy val` or an overridable member). In `h.f`, the prefix `h` is a stable `val` of a class built by `new`, and `f` is itself a stable `val`, so neither is examined. On this catalogue `-source future` changes no verdict.
- **"`-Yexplicit-nulls` rejects the `null` paths."** This holds: every program that throws under another setting is rejected ("Found: Null, Required: A & B"), and so is every control that uses `null`.

The first space (step 3) therefore takes the two-views shape as its core, since it is the one all three compilers can express. It keeps the intersection view for Scala 3.
