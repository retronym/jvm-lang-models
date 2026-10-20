# Phase 31 — Forwarders: mixin and static, against the Merkle rules

20 October 2026. Prompted by the Merkle PoC bug fixed in retronym/zinc `fdafc0a4a` (the `mirror` rule missed an object whose ancestor is nested in, or reached through, an object, and a Java client calling the static forwarder failed with `NoSuchMethodError`).

## Summary for a busy reader

Both kinds of forwarder were already in the lowering model ([`Scala.classBody`](../../scala/Scala/Lower.lean#L249) for mixin forwarders, [`Scala.forwarders`](../../scala/Scala/Lower.lean#L429) for static ones) and in the Merkle model's codegen queries ([`Flat.mixinFwds`, `Flat.staticFwds`](../Zinc/Bridges/Flat.lean)), from which `traitDirect` and `mirror` are derived. This phase models each kind from the compiler's source (scalac 2.12.21 and 2.13.18, the latest releases, which agree on both), calibrates the lowering model against those compilers and dotc 3.9.0, writes down what each kind reads, and checks each read against Zinc's descendant rules with scripted tests.

- **One lowering bug, fixed.** The model gave a nested companion pair static forwarders. scalac never does (`!lmoc.isNestedClass`); dotc does when the object is static (`lmoc.isStatic`: nested in objects, not in a class). The fix is in `lowerSrc`; `nestSpace` gains a nested pair and a new `fwdSpace` holds the shapes read off the source. Calibration: 1,353 of 1,353 programs agree for 2.12.21 and for 2.13.18, 1,368 of 1,368 for 3.9.0.
- **Mixin forwarders match `traitDirect`.** Zinc's `mixesIn` is scalac's `mixinClasses`, including a trait mixed in through another trait (`merkle-trait-indirect-mixin` passes).
- **Static forwarders read two things the `mirror` rule does not cover.** Both are covered today only because `conflicts` happens to fire. Dropping `conflicts` makes both fail, so the forwarders hang on a rule that was written for something else:
  1. *The companion class's member names, inherited ones too* (scalac's `conflictingNames`). An ancestor of `class C` gaining `k` removes the static forwarder for `object C`'s `k`. `mirror` asks only whether the object half inherits the changed class.
  2. *Scala 3, a companion pair nested in an object.* `Top$N` has static forwarders, but `mirror` requires `isTopLevel`. Without `conflicts`, a Java client gets `NoSuchMethodError: 'int p.Top$N$.m()'`. With it, `conflicts` fires as "also inherits m", which is not a conflict: `A` is the only declarer, so the rule fires through a name mismatch on the path filter.

## Mixin forwarders

**What scalac does** (`Mixin.mixinTraitForwarders`, the same in 2.12.21 and 2.13.18 but for a refactor). For each class or object `C` (not a trait), and each trait `T` in `C.mixinClasses` (every trait in `C`'s linearization that is not in its superclass's, so a trait reached through another trait counts), and each `T` declaration `m` that is a concrete method, not private, not an accessor (a `lazy val`'s is), not overridden in `C` and `C`'s member under its name and signature: a forwarder `C.m` to `T.m$`. Under the default `-Xmixin-force-forwarders:true` it is emitted whether the JVM needs it or not; `required` only decides whether a Java interface not directly extended is an error. The forwarder is created after erasure, so its descriptor is `m`'s erasure in `T`, and a bridge covers `C`'s view.

**What it reads.**

| read | Merkle rule |
|---|---|
| the declarations of each trait in `mixinClasses(C)` | `traitDirect`: `mixesIn(C, T)` is "`C` is not a trait, `T` is in its linearization, no class ancestor has `T`", which is `mixinClasses` |
| whether an ancestor ahead of `T` declares `m` (the forwarder exists only if `T`'s member wins) | ancestors ahead of `T` are `C` itself and the traits mixed in after it, all in `mixinClasses`, so `traitDirect` again; `overrides` for `C` |
| the erasure of `m`'s signature in `T` (a value class's underlying type) | the erasure key of Phase 6 |

No gap. `merkle-trait-indirect-mixin` (a trait mixed in through another) passes.

## Static forwarders

**What scalac does** (`BCodeHelpers.addForwarders`, called from `CodeGen` for a mirror class and from `BCodeSkelBuilder.initJClass` for a companion class; identical in 2.12.21 and 2.13.18 but for the dropped `isRemote`).

- *Where.* A top-level object without a companion class gets a mirror class; a companion class (or trait: `trait T; object T extends A` puts `static k()` in the interface) gets them when `lmoc` is not nested. Nothing for a nested pair in Scala 2. dotc's test is `lmoc.isStatic`, so a pair nested in an object gets them too.
- *Which members.* `moduleClass.info.membersBasedOnFlags(SPECIALIZED | LIFTED | PROTECTED | STATIC | EXPANDEDNAME | PRIVATE | MACRO, METHOD)` at `exitingUncurry`, so before bridges and before the fields phase adds trait setters, minus deferred members, constructors, `private[q]` (`hasAccessBoundary`), members of `Object`, `AnyRef` and `Any`, and **every name in `conflictingNames`, the term names of `linkedClass.info.members`, inherited ones included**. Overloads each get one. A `var`'s setter `x_$eq` is forwarded; a trait setter is not.
- *Descriptor.* The member's erasure in its owner, not as seen from the object ([scala/bug#3452](https://github.com/scala/bug/issues/3452): `object O extends G[String]` gets `g(Object)Object`), and the body is `MODULE$.m` with that descriptor.

All of these were probed against both compilers in a scratch program before being added to the space. Overloads within one class are outside the model's subset (`ScalaTypes.Syntax`), and the model emits one of the two.

**What it reads.**

| read | Merkle rule | status |
|---|---|---|
| the members of every ancestor of the object, with access | `mirror`: `isTopLevel(d) && objectInherits(d, p)` | covered; names compared canonically since `fdafc0a4a` |
| the erasure of each member in its owner | the erasure key of Phase 6 | covered (`value-class-mirror-forwarder`) |
| the term names of the companion class, its own and inherited | none named; `conflicts` fires because Zinc merges the pair's ancestors, and the object's parent declares the name | `merkle-mirror-companion-shadowed` passes; with `descendantRules = -conflicts` the stale `static C.k` survives (`-no-conflicts`, pending) |
| whether the object is static (Scala 3) or top-level (Scala 2) | `mirror` takes top-level for both | `merkle-mirror-nested-companion-scala3` passes through `conflicts` ("also inherits m", a name mismatch on the path filter); with `-conflicts` it fails with `NoSuchMethodError` (`-no-conflicts`, pending) |

The `Flat` model cannot reach either gap: its classes are top-level, its objects have no companion class, and its `mirror` rule is "`d` is an object". Its `staticFwds` reads the ancestors' declarations, not a companion's names.

## What would close the gaps in Zinc

- `mirror` fires for a pair with a companion class when the changed class is an ancestor of *either* half, since the class half's names decide which forwarders exist. That is the rule the read set asks for; today `conflicts` gives it by accident of the merged pair.
- `isTopLevel` becomes "top-level, or (Scala 3) nested only in objects". For Scala 2 the present test is right.
- The two `-no-conflicts` tests leave `pending` when `mirror` alone passes them.

## Evidence

- Lowering: `probe.py` against scalac 2.12.21, 2.13.18 and dotc 3.9.0, no divergence shapes. The same change models the `InnerClasses` entries of a nested pair: the class lists the module in Scala 3 only, and the module lists the class only when it names it (a case class's `apply`).
- Zinc: retronym/zinc branch `claude/merkle-forwarder-model-tests` on `fdafc0a4a` (`merkle-mirror-nested`), scripted tests `merkle-trait-indirect-mixin`, `merkle-mirror-companion-shadowed`, `merkle-mirror-nested-companion-scala3` (pass) and the two `-no-conflicts` ablations (fail, marked pending).

## Future work

- [ ] A companion half in `Flat` (or a `Companions`-style space with forwarders) so the exhaustive check sees `conflictingNames`.
- [ ] The two `mirror` changes above in Zinc, and the `-no-conflicts` tests unpended.
- [ ] Overloads in one class, `protected` and `private[q]` members in the language subset; the static forwarder rules for them are known from the source and probed, but the model cannot state them.
