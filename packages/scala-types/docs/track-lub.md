# Track LUB — How scalac and dotc join types

21 October 2026.

## Summary for a busy reader

Whenever a Scala compiler infers the type of `if (c) a else b`, of `List(a, b, c)` or of a match, it computes a *join*: an upper bound of the branches' types. In a lattice the join would be unique and the laws would come for free: commutative, associative, idempotent. Scala's types are not a lattice. With traits there is often no least upper bound, only several incomparable minimal ones (`S extends Zed with Abe`, `T extends Abe with Zed`: both `Zed with Abe` and `Abe with Zed` are minimal, and they are equivalent but not the same type); with F-bounds the least one is infinite; with refinements it is a structural type nobody wrote. So each compiler *chooses*, and what a choice depends on is what this track is about. The answer matters beyond type checking, because the chosen type is the method's signature: its erasure is the JVM descriptor that callers link against, and its order of parents is what Zinc hashes.

The probe ([`probes/lub/lub.py`](../probes/lub/lub.py), worlds in [`worlds.py`](../probes/lub/worlds.py), results in [`results.txt`](../probes/lub/results.txt)) infers 1,086 joins over 16 small hierarchies on each of scalac 2.12.21, 2.13.18 and dotc 3.9.0, jointly and against the hierarchy's classfiles, and checks the laws. The model ([`ScalaTypes/Lub.lean`](../ScalaTypes/Lub.lean)) states both algorithms over a class hierarchy and proves or refutes the laws. What we found:

1. **scalac's join is commutative and associative over classes, and depends on symbol ids.** It sorts parents by `Symbol.isLess` (deeper base type sequence first, then symbol id), so the result is a function of the *set* of inputs ([`lubS_comm`](../ScalaTypes/Lub.lean#L187)); every permutation of every triple agrees. But ids follow creation order, so the same sources give `Zed with Abe` (erased to `Zed`) jointly and `Abe with Zed` (erased to `Abe`) against classfiles ([`lubS_ids`](../ScalaTypes/Lub.lean#L257); measured: all 36 joins of the `traits` world change descriptor). Known: [scala/scala#11291](https://github.com/scala/scala/issues/11291) breaks the tie by name ([`lubS_byName`](../ScalaTypes/Lub.lean#L264)).
2. **scalac's `glb` is not sorted, and leaks into lubs.** A join of `Inv[Int]` and `Inv[String]` is `Inv[_ >: Int with String]`, whose lower bound is a glb in *branch* order; `if (c) inv1 else inv2` and `if (c) inv2 else inv1` have different Java generic signatures (`Inv<-Object>` against `Inv<-String>`), and `List(inv1, inv2)` has the opposite order to `if (c) inv1 else inv2`. Same for F-bounded and `Comparable` joins. Finding LUB2.
3. **dotc's parents follow the first branch.** `orDominator` intersects base classes in the first operand's linearization order, so `if (c) s else t` is `Zed & Abe` and `if (c) t else s` is `Abe & Zed` ([`joinD_order`](../ScalaTypes/Lub.lean#L268)); as sets they agree ([`joinD_comm`](../ScalaTypes/Lub.lean#L229)). Unlike scalac this is stable across separate compilation (TASTy keeps the linearization), and dotc erases intersections by a total order, so the descriptor does not change.
4. **dotc keeps a union when its join is uninformative, and that breaks associativity.** `widenInferred` widens a union in a `val`'s type to its join unless every part of the join is transparent (`Object`, `Product`, `Serializable`, `Comparable`, ...), in which case the union is kept. So `val t = if (c) circle else square` is `Shape`, `if (c) t else other` is `Shape | Other`, but `List(circle, square, other)` is `List[Circle | Square | Other]`: two types that are not even equivalent (`Point` is in one only). Extracting a `val` changes an inferred type ([`widenD_not_assoc`](../ScalaTypes/Lub.lean#L291)). By design; finding LUB4.
5. **A kept union is erased by its first operand.** `if (c) l else n`, with `L extends Product with Serializable` and `N extends Serializable with Product`, erases to `java.io.Serializable`; swap the branches and it erases to `Product` ([`eraseUnion_order`](../ScalaTypes/Lub.lean#L311)). Known: [scala/scala3#24148](https://github.com/scala/scala3/issues/24148) identified the inverted cut in `erasedLub`; the model adds that removing the negation alone does not give symmetry ([`eraseUnion_fixed_order`](../ScalaTypes/Lub.lean#L317)), while erasing the join as the specification says does ([`eraseJoin_symm`](../ScalaTypes/Lub.lean#L330)).
6. **Each compiler rejects a join the other accepts.** With `trait Fb[+T <: Fb[T]]`, scalac infers `Fb[Fb[Object]]` for `if (c) new Fa else new Fc`, cut off by `lubDepth` with `Object` inside, and rejects its own inference as ill-bounded; dotc infers `Fb[Fa | Fc]`. With an invariant `Fb[T <: Fb[T]]` it is the other way round ([scala/scala3#9941](https://github.com/scala/scala3/issues/9941), known). Finding LUB3, with a [draft](../../../docs/upstream/scalac-fbound-covariant-lub.md).
7. **Equivalent inputs: the first wins.** `if (c) k else kk` with `type KK = K` is `K`, swapped it is `H.KK`, in all three compilers (`maxTypes` and `dropIfSub` keep the first of mutual subtypes; [`lubS_alias`](../ScalaTypes/Lub.lean#L274)). Harmless up to `=:=`, recorded so the laws are stated up to equivalence.

The rest of this note explains each algorithm, the laws and where they fail, the probe and the model.

## 1. Why there is no least upper bound

In a nominal language with single inheritance the join of two classes is their nearest common superclass: unique, and the laws hold. Traits make the common supertypes a set with several minimal elements. Scala 2's answer is to take *all* minimal common base classes and intersect them, `Zed with Abe`, which is a least upper bound up to equivalence — and `with` is not commutative as syntax: `Zed with Abe` and `Abe with Zed` are equivalent types with different erasures, different generic signatures and different Zinc API hashes. So the question "which join" becomes "which order", and an order needs a key. Neither "the order the programmer wrote" nor "the order of declaration" is a property of the types; scalac uses symbol ids, which are not even a property of the program.

Type constructors make it worse. The join of `Fa extends Fb[Fa]` and `Fc extends Fb[Fc]` is `Fb[X]` where `X` is the join of `Fa` and `Fc` again: the least upper bound is the infinite `Fb[Fb[Fb[…]]]`. scalac cuts it at a depth computed from the inputs (`lubDepth`), and what it puts at the cut must still be a valid type. Refinements add structural members: scalac gives the join of `R1 { def m: Int }` and `R2 { def m: Int }` the refinement `R { def m: Int }` (the probe's `refine` world), a type nobody wrote, and its members' types are joins at a smaller depth.

Scala 3's answer is different in kind: the join is a union, `A | B`, which *is* least, and commutative and associative up to equivalence. But a union is a poor type to put in a signature, so dotc widens it (`widenUnion`) when inferring the type of a `val` or `def`, and the widening is where the choices come back.

## 2. scalac: base type sequences and depth

`GlbLubs.lub(ts)` ([2.13.18](https://github.com/scala/scala/blob/v2.13.18/src/reflect/scala/reflect/internal/tpe/GlbLubs.scala)):

* **`elimSub`**: drop every input that is a subtype of another (`maxTypes`). Of two mutual subtypes the first survives.
* **`lubList`**: walk the inputs' *base type sequences* in step. A base type sequence is a type's base types sorted by `Symbol.isLess`: deeper sequence first, ties broken by symbol id (by name in [scala/scala#11291](https://github.com/scala/scala/issues/11291)). The walk advances a frontier past the least symbol until every column's head has the same symbol, then merges their prefixes and type arguments (`mergePrefixAndArgs`: covariant arguments are lubbed, contravariant ones glbbed, invariant ones become an existential with a glb as lower and a lub as upper bound), each at `depth - 1`.
* **`spanningTypes`**: of the common base types, keep the ones not already implied by an earlier one. These are the parents, in `isLess` order.
* **`lubRefined`**: at nonzero depth, for every member all inputs refine (`excludeFromLub` aside), add a refinement whose type is the join of their types at `depth - 1`.
* **`lubDepth`**: the depth is the inputs' type depth and base type sequence depth, adjusted down for deep sequences (`lubDepthAdjust`). At negative depth `lub` returns `Any`; that is the `Object` in `Fb[Fb[Object]]`.

Two memo tables (`lubResults`, `glbResults`) cache results per depth during one top-level call and double as recursion guards; [scala/bug#13202](https://github.com/scala/bug/issues/13202) (known, [scala/scala#11313](https://github.com/scala/scala/issues/11313)) shows a nested top-level lub reading the outer one's guard. `glb` sorts nothing: `elimSuper` keeps input order, and the intersection is built in that order.

**Where the order comes from.** `isLess` is a total order once ids are distinct, so the parents of a join do not depend on the order of the inputs. They depend on the ids, which follow symbol creation: declaration order for sources in the batch, file-name order for a classpath directory, hash-map order for a jar ([scala/scala#11291](https://github.com/scala/scala/issues/11291)'s account). The probe's `traits` world measures it: every one of the 36 joins erases to `Zed` jointly and to `Abe` separately, on both 2.12.21 and 2.13.18.

## 3. dotc: unions, joins and widening

`TypeComparer.lub` ([3.9.0](https://github.com/scala/scala3/blob/3.9.0/compiler/src/dotty/tools/dotc/core/TypeComparer.scala)) forms `A | B`, after dropping an operand that is a subtype of the other (`dropIfSub`). `List(a, b, c)` folds it left. In a `val`'s or `def`'s inferred type, `ConstraintHandling.widenInferred` then:

* widens the union to its **join** (`OrType.join` = `TypeOps.orDominator`): intersect the operands' base classes, walking the *first* operand's linearization, keep the dominators (those no other common base class derives from), accumulated by prepending, and intersect their base types (with `lubArgs` for type arguments: covariant joined, contravariant met, invariant a wildcard with both bounds);
* **keeps the union** if the join is transparent (`isTransparent`: every class in it is `Any`, `Object`, `Matchable`, `Product`, `Serializable`, `Comparable` and the like, or a `transparent trait`): `Int | String`, `Circle | Other`, `Some[Int] | Left[Int, Nothing]` are inferred as unions;
* otherwise **drops transparent traits** from the intersection (`dropTransparentTraits`): `Shape & Product & Serializable` becomes `Shape`.

Unions written by the programmer are hard and not widened. The design choice that matters here: whether a union survives depends on the *whole* union's join, so it is not compositional. Joining two of three types first and the third afterwards is a different question from joining all three.

**Erasure.** An intersection erases by `erasedGlb`, the minimum of a total order (classes before traits, then by full name): commutative. A union erases by `erasedLub(tp1, tp2)`, which walks `tp1`'s base classes; [scala/scala3#24148](https://github.com/scala/scala3/issues/24148) notes that its `takeUntil(…)(!_.is(Trait))` stops at the first trait rather than the first class, against its own comment. The probe reaches it with no union written: `if (c) l else n` and `if (c) n else l` compile to different descriptors, and a subclass overriding one with the other gets a bridge.

## 4. The laws, per compiler

Measured over the 16 worlds of [`results.txt`](../probes/lub/results.txt) (each law instance is a pair or set of inferred `val` types compared as printed; "order" means equal after sorting the operands of every `&`, `|` and `with`):

| law | scalac 2.12.21, 2.13.18 | dotc 3.9.0 |
|---|---|---|
| commutativity `x ⊔ y = y ⊔ x` | holds over classes; fails in the order of a glb inside (`Inv[_ >: Int with String]` against `Inv[_ >: String with Int]`, F-bounds, `Comparable`), changing the generic signature; fails for equivalent inputs (aliases) | parents and union operands follow the first operand; erasure of a kept union changes; fails for equivalent inputs |
| permutations of `List(x, y, z)`, match arms | as commutativity | as commutativity |
| associativity `(x ⊔ y) ⊔ z = List(x, y, z)` | holds over classes; for invariant and F-bounded joins only up to equivalence (nested existentials) | **fails up to equivalence**: `Shape \| Other` against `Circle \| Square \| Other`, `Long \| Char` against `Int \| Long \| Char`, `Option[Int] \| Left[...]` against `Some[Int] \| None \| Left[...]` |
| absorption `(x ⊔ y) ⊔ x = x ⊔ y` | holds over classes; for an invariant or F-bounded join, an equivalent but different existential `Inv[_1] forSome { type _1 >: _1 with Int; type _1 >: Int with String }`, two binders printed with one name | holds |
| separate compilation | **fails**: parent order and erasure follow symbol ids ([scala/scala#11291](https://github.com/scala/scala/issues/11291)) | holds |
| well-formed result | **fails** for a covariant F-bound (LUB3) | **fails** for an invariant F-bound ([scala/scala3#9941](https://github.com/scala/scala3/issues/9941)) |

Across compilers the joins differ by design: 2.12 and 2.13 differ in `Serializable` (`scala.Serializable` against `java.io.Serializable`), scalac infers refinements dotc drops, dotc keeps unions scalac cannot express. The library world also shows that an inferred type can depend on the JDK: on JDK 21 the join of `String` and `Integer` includes `java.lang.constant.Constable with ConstantDesc`, which JDK 11 does not have (they arrived in JDK 12).

## 5. The model

[`ScalaTypes/Lub.lean`](../ScalaTypes/Lub.lean) states a hierarchy of classes and traits with Scala linearization (`lin`), then:

* scalac: `isLess` with a tie-break by id table or by name, base type sequences as the one `isLess` order restricted to a class's base classes, `stacked` (the `maxTypes` of `elimSub`), `lubList` and `spanningF`, and `eraseS` (`intersectionDominator`);
* dotc: `commonD` and `doms` (`orDominator`), `joinU` and `widenD` over unions of intersections (`widenInferred` with transparency and `dropTransparentTraits`), `eraseUnion` with the cut as written and as intended, and `eraseJoin` (the specification's erasure).

Proved for every hierarchy: scalac's join of two unrelated classes is commutative ([`lubS_comm`](../ScalaTypes/Lub.lean#L187)) and an upper bound ([`lubS_upper`](../ScalaTypes/Lub.lean#L208)); dotc's join has the same parents in either order as a set ([`joinD_comm`](../ScalaTypes/Lub.lean#L229), via [`doms_mem`](../ScalaTypes/Lub.lean#L218)) and is an upper bound ([`joinD_upper`](../ScalaTypes/Lub.lean#L236)). Refuted on the probe's worlds, each by `decide` and each matching `results.txt`: [`lubS_ids`](../ScalaTypes/Lub.lean#L257), [`lubS_alias`](../ScalaTypes/Lub.lean#L274), [`joinD_order`](../ScalaTypes/Lub.lean#L268), [`widenD_not_assoc`](../ScalaTypes/Lub.lean#L291), [`eraseUnion_order`](../ScalaTypes/Lub.lean#L311), [`eraseUnion_fixed_order`](../ScalaTypes/Lub.lean#L317); and the counterpart that holds, [`eraseJoin_symm`](../ScalaTypes/Lub.lean#L330).

The model is deliberately at the level of classes: no type arguments, no refinements, no depth. That is enough for the order and associativity questions, which are about which classes and in which order, and it is where the compilers' algorithms are simple enough to state in a page.

## 6. Why it matters

* **Reproducible builds.** A classfile should be a function of its sources. scalac's id-order makes it a function of the compilation batch, so an incremental build (Zinc compiles the changed files against the rest's classfiles) and a clean one differ in descriptors, which is what [scala/scala#11291](https://github.com/scala/scala/issues/11291) found in Spark. dotc is stable here.
* **Binary compatibility by accident.** Swapping two branches of an `if` is a refactoring nobody reviews for ABI. In dotc it can change a public method's descriptor (a kept union), and in both compilers it changes the generic signature (scalac's glb order) or the TASTy/pickled type (dotc's parent order). MiMa would report the descriptor change; Zinc's API hash sees the type change and recompiles dependents, correctly but unnecessarily.
* **Refactoring changes types.** In dotc, extracting a subexpression into a `val` can change the inferred type of the expression that uses it to a non-equivalent one (LUB4). A smaller type, `Circle | Square | Other`, is lost for a larger one, `Shape | Other`; code that pattern-matches exhaustively on the result sees `Point` appear.

## 7. Future work

* **Type arguments and depth in the model.** `mergePrefixAndArgs` and `lubDepth`, to state LUB3 (the truncated argument violates the bound) and scalac's associativity-up-to-equivalence for F-bounds.
* **glb.** scalac's unsorted `glb` (LUB2) as a model of its own, and dotc's `&` with `erasedGlb`'s total order (commutative, proved upstream by construction).
* **Refinements.** scalac's `lubRefined` and dotc's treatment of structural members (the `refine` and `anon` worlds: scalac `R{def m: Int}`, dotc `R`, and dotc's anonymous classes keep a refinement of `m` only).
* **The fixed tie-break, measured.** Rerun the probe against a build of [scala/scala#11291](https://github.com/scala/scala/issues/11291) and of [scala/scala#11313](https://github.com/scala/scala/issues/11313): the `traits` world should then agree jointly and separately.
* **Zinc.** Phase 15-style: a type whose parent order changes between an incremental and a clean build is an API change Zinc must see; check that its API hash orders a compound type's parents as written.
