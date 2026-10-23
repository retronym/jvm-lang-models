# Track P: phases, the schedule a compiler pretends to be

A Scala compiler is described as a pipeline: typer, then a few dozen phases, each taking trees and symbol infos to lower ones. The description is a useful fiction. What runs is a schedule: phases share mutable objects, run fused, and answer questions about other phases' views of the world. This track measures where the fiction breaks in scalac 2.12/2.13 and dotc 3.9, and states the obligations that keep it true.

## Summary for a busy reader

* **Two kinds of transformer, one shared world.** A tree transformer rewrites the trees of the unit at hand. An info transformer rewrites a symbol's type, lazily, the first time someone asks for it at or after its phase. Info transforms are global and on demand; tree transforms are local and in order. Every phase-ordering bug in this track is a place where one of them assumes the timing of the other.
* **Scopes are mutated, not copied** ([`Scopes.lean`](../../scala-types/ScalaTypes/Scopes.lean)). A class's `Scope` is one object shared by a run of phases until an info transformer builds a new one. A member entered by a tree transformer is therefore visible, after the run, from the start of the version it landed in, not from the phase that added it. The obligation ([`late_eq_truth_iff`](../../scala-types/ScalaTypes/Scopes.lean#L55)): an entry must land in a version that starts exactly where the member should become visible. dotc's `enteredAfter(thisPhase)` meets it by construction ([`enteredAfter_sound`](../../scala-types/ScalaTypes/Scopes.lean#L97)). scalac's LambdaLift does not, and says so in a TODO; some dotc transforms use plain `entered` and do not either.
* **Fusion is not transparent** ([`Fusion.lean`](../../scala-types/ScalaTypes/Fusion.lean)). dotc runs a group of miniphases in one traversal, all at the phase after the group's last miniphase. Compiling dotty's `tests/run` with every miniphase in its own group instead changes the output of 83 of 1549 files that compile, crashes on one, and in one changes what the program prints. Fusion is transparent when an earlier miniphase only relabels the node it is given ([`fused_eq_seq_of_relabel`](../../scala-types/ScalaTypes/Fusion.lean#L87)); the measured differences are each a way out of that condition.
* **Asking about the future early** (§4). In scalac, forcing infos at flatten right after pickler changes the output of 1101 of 1431 `test/files/run` programs and crashes 102. Info updates are guarded and fail loudly; scope copies and two memoized names are not and fail silently, down to emitting `m$E.class` for a local class.
* **One bug in the shipped compiler.** `DropOuterAccessors` runs fused with `Flatten`, so it sees owners after Flatten, and never drops the outer accessor of a named nested class that `CountOuterAccesses`, in the group before, counted as droppable ([`dotc-drop-outer-accessors-fused.md`](../../../docs/upstream/dotc-drop-outer-accessors-fused.md)).

## 1. Tree transformers, info transformers

scalac's `InfoTransform` and dotc's `DenotTransformer` give a phase two hands. The tree hand runs once per unit, in phase order: all units finish phase `p` before any starts `p + 1`. The info hand runs per symbol, whenever someone asks `sym.info` at a phase past `p` and the cached answer is older: in the middle of another unit, in the middle of another phase, or from the backend after the run. Neither compiler stores every phase's answer:

* scalac keeps a `TypeHistory` per symbol (the infos, by validity), a phase mask for the flags, and one slot for the name and owner;
* dotc keeps a denotation per validity period, so a symbol's name, owner, flags and info at a phase are all recoverable.

So the info hand is lazy and memoized ([Track L](track-l.md) §5 measures the overwritten slots), and the tree hand is eager. The lazy hand is safe only if what it computes does not depend on when it runs. The rest of this note is about the things it does depend on.

## 2. Scopes: mutated, not copied

A class's declarations are part of its info (`ClassInfoType(parents, decls, cls)`), but the `decls` object is mutable. An info transformer that changes nothing returns the same `ClassInfoType`, so consecutive phases share one `Scope`. A tree transformer that adds a member (a lifted class, a mixin forwarder, a lazy-val holder, a static moved to the companion) enters it into "the" scope: the object current at whatever phase it names.

[`Scopes2.scala`](../probes/phases/Scopes2.scala) records each class's declarations after every phase during the run and asks again after it. It also prints which phases' answers are one object. For `object C { def m: AnyRef = { class E; new E } }`, scalac 2.13.18:

```
== C$  scopes: typer patmat | uncurry fields | specialize posterasure lambdalift constructors | flatten mixin
  specialize     after the run, added: cla E$1
  posterasure    after the run, added: cla E$1
```

LambdaLift entered `E$1` into the scope that SpecializeTypes' info transformer made, so after the run `E$1` is a declaration "exiting specialize", three phases before it existed. The source agrees: above `sym.owner.info.decls enterUnique sym` in `LambdaLift.scala`,

> This breaks type history: in a phase travel to before lambda lift, the ClassInfoType will contain lifted classes.

How far back the leak reaches is an accident of which info transformers happen to copy. SpecializeTypes copies every class it might specialize (`newScopeWith`). With `-no-specialization` it does not, and `E$1` leaks back to "exiting uncurry". Other copies are conditional too: UnCurry copies when there are `@varargs` overloads, ExplicitOuter for inner classes, Fields when it adds fields, and Flatten always (`newScope`). Mixin's trait forwarders land in Flatten's copy, so they appear "exiting flatten" ([`mixinForwarder_from_flatten`](../../scala-types/ScalaTypes/Scopes.lean#L133)).

dotc versions scopes: `enteredAfter(thisPhase)` installs a new denotation for the class, starting at the next phase, and enters the member there. Twenty-seven calls in `transform/` do. About nineteen use plain `entered`, which mutates the current denotation's scope, and [`Scopes3.scala`](../probes/phases/Scopes3.scala) finds the ones that matter ([`scopes-3.9.0-features.txt`](../probes/phases/scopes-3.9.0-features.txt)):

* `SpecializeFunctions` adds `apply$mcII$sp` to `class F extends (Int => Int)`, visible at typer after the run;
* `MoveStatics` moves `@static val t` from `object S` to `class S` with `entered` and `unlink`, so at typer after the run `S` has `t` and `S$` does not;
* `CompleteJavaEnums` adds `_$name` and `_$ordinal`, and `SyntheticMembers` adds `writeReplace`, both visible at typer.

### The obligation, and who discharges it

[`late_eq_truth_iff`](../../scala-types/ScalaTypes/Scopes.lean#L55) states it exactly. Late answers equal the intended ones at every phase if and only if each entry lands in a version that starts at the phase from which the member should be visible. There are three ways to live with a compiler that does not meet it:

1. **Meet it.** dotc's `enteredAfter`. Fields does this by hand ("must not alter `decls` directly").
2. **Read through a filter.** A reader at an earlier phase excludes what later phases could have added. scalac's static forwarders read `exitingUncurry(...membersBasedOnFlags(ExcludedForwarderFlags, METHOD))`, and the excluded flags include `LIFTED` and `PRIVATE`. A local method lifted into an object's scope under `-no-specialization` is in the uncurry-phase answer and is still not forwarded. The comment above that read shows the obligation was found the hard way: "erasure enters bridges in traversal, not in the InfoTransform, so it actually modifies the type from the previous phase" ([scala/bug#10812](https://github.com/scala/bug/issues/10812)).
3. **Read only where it is safe.** The backend's `exitingPickler(memberClassesForInnerClassTable(cls))` relies on the pickler-phase scope not sharing an object with LambdaLift's. That holds because UnCurry (and SpecializeTypes) happen to copy in between, not because anything guarantees it.

Copies being lazy adds a second hazard. A version copied before an entry into its predecessor never gets the entry ([`copy_before_entry`](../../scala-types/ScalaTypes/Scopes.lean#L179)). dotc had exactly this bug, [scala/scala3#440](https://github.com/scala/scala3/issues/440), and fixed it by making `enter` also enter later versions. scalac's equivalent is a phase travel forward (`exitingFlatten { cls.info }`) during an earlier phase, which forces Flatten's copy too soon.

The leaks above are latent: no reader in either compiler is known to see them. They are what makes "ask the compiler at phase p" a question whose answer depends on when it is asked. Every IDE, debugger and macro that phase-travels inherits that.

## 3. Fusion

dotc groups miniphases and runs each group in one traversal (`MegaPhase`). At each node, once its children are done, every miniphase of the group transforms the node in turn. The alternative is to run each miniphase over the whole tree before the next starts. The two schedules agree only under conditions:

* **An earlier phase sees a later one's output.** Fused, miniphase `f` transforms a node whose children `g` (later in the group) has already rewritten. `ExtensionMethods` positions a value class's forwarder at its method's right-hand side (`fwd.withSpan(originalDef.rhs.span)`). Fused, `PatternMatcher` has already replaced that `match`, so the forwarder's line number differs (`tests/run/19384.scala`; [`reads_child`](../../scala-types/ScalaTypes/Fusion.lean#L115)).
* **A later phase never sees what an earlier one creates.** Fused, `g` sees only the root of what `f` returned, so a phase that synthesizes trees must hand them to the rest of its group itself: `transformFollowing` and `transformFollowingDeep`. Mixin says why: "transformFollowing call is needed to make memoize & lazy vals run" ([`creates_subtree`](../../scala-types/ScalaTypes/Fusion.lean#L126), [`creates_subtree_following`](../../scala-types/ScalaTypes/Fusion.lean#L138)).
* **A pre-pass sees the group's input.** `CapturedVars.prepareForUnit` collects the mutable locals that closures capture by traversing the unit before the group runs. Fused, `LazyVals` (same group) has not yet made a local lazy val's holder, which is `Synthetic | Mutable | Lazy`. Unfused it has, and `CapturedVars` boxes the holder in an `ObjectRef`, which is correct but pointless (57 of the 83 files).
* **A miniphase meets siblings in another order.** A parent's transform can hand trees it creates to the rest of the group (`transformFollowing`) *after* its children have been transformed, so fused, a later miniphase transforms those new trees after the parent's own children, whatever their place in the tree; unfused, it meets them in tree order. That matters when the miniphase passes facts between siblings through the symbol table: Memoize's transform of a getter enters a field that its transform of a setter then looks up by name. That is #25108 below.
* **Every miniphase runs at the group's end.** `MegaPhase.run` is `atPhase(miniPhases.last.next)`, since [scala/scala3#3350](https://github.com/scala/scala3/pull/3350) (6–7% faster). So a miniphase sees the infos that later miniphases in its group produce. That is the DropOuterAccessors bug below.

The probe is [`Fusion3.scala`](../probes/phases/Fusion3.scala), with [`fusion_classify.py`](../probes/phases/fusion_classify.py). Over `tests/run/*.scala` ([`fusion-3.9.0-run.txt`](../probes/phases/fusion-3.9.0-run.txt)), 1465 files are byte-identical and 83 differ. The differences: lazy-holder boxing in 57+11; outer accessors or fields kept fused and dropped unfused in 13; line numbers in 2; the order of lazy-val fields and of their `VarHandle`s; a `getfield` of `Tuple2$mcII$sp._1$mcI$sp` unfused where fused calls the accessor; and the two bugs below. One file crashes unfused. The first 1400 files of `tests/pos` ([`fusion-3.9.0-pos.txt`](../probes/phases/fusion-3.9.0-pos.txt)) show the same three mechanisms and nothing else: 45 differ, none crashes.

**A bug in the shipped compiler, whose fused output is the wrong one** ([scala/scala3#25108](https://github.com/scala/scala3/issues/25108)). `tests/run/final-fields.scala`, minimized in [`fusion/traitSetter.scala`](../probes/phases/fusion/traitSetter.scala):

```scala
trait T { val f4: Int = { println("T.f4"); -4 }; println(f4) }
object Test extends T { override val f4 = 4; def main(args: Array[String]) = println(f4) }
```

Scala 2.13.16 prints `T.f4 0 4`, and so does dotc with every miniphase in a group of its own. Shipped dotc (3.7.3 here; the checkfile has read `-4` since [11de1d3667](https://github.com/scala/scala3/commit/11de1d3667), 2020, and read `0` before) prints `T.f4 -4 4`. Mixin gives `Test` an implementation of the trait setter `T$_setter_$f4_$eq`, with a `()` body, and, because `Test` overrides `f4`, no forwarder for `T`'s getter. `Memoize` then gives the setter an assignment if `sym.field` exists, and `sym.field` looks the field up *by name*: the name `f4` is shared with `Test`'s own `val f4`. Unfused, Memoize walks the template in order, reaches the setter (which Mixin put first) before the getter, finds no field and keeps `()`: the right answer. Fused, Mixin passes the setter through `transformFollowing` when it leaves the template, after the getter of `Test.f4` has made its field (the sibling-order case above), so the setter writes the trait's `-4` into the overriding val's field, where `T`'s initializer reads it. Where the override narrows the type, the setter's cast throws `ClassCastException`, which is how #25108 was reported.

This is [Track L](track-l.md)'s peek: the absence of a fact not yet established is read as a negative answer. Here the question itself was wrong (a field by that name, rather than a field for that val), and the shipped schedule is the one that gives the wrong answer to it. The fix ([retronym/scala3#70](https://github.com/retronym/scala3/pull/70)) asks what Mixin had settled instead: whether the class inherits the trait's getter. Over an exhaustive matrix of trait, class and object overrides of a `val`, `var` or `def` ([gist](https://gist.github.com/retronym/55cfd07e35337a18ed1aaae0e80ca692)), with Scala 2 as the oracle, the shipped fused compiler differs in 740 of 4,368 programs, unfused in none, and with the fix in none either way.

**A bug in the shipped compiler.** `CountOuterAccesses` counts uses of outer accessors that `mightBeDropped`, and `DropOuterAccessors`, a group later, drops the unused ones. `mightBeDropped` depends on the class's owner and top-level class. `DropOuterAccessors` shares its group with `Flatten` and runs at the group's end, so it sees every nested class already moved to its package and answers false. Shipped dotc 3.9.0 keeps `Q$_$M$$$outer()` on a local class and `Q$I$$$outer()` on a private member class, unused. Unfused it drops them, and then hits an assertion on a trait's deferred accessor (`tests/run/llift.scala`), which a fix must also handle. Draft: [`dotc-drop-outer-accessors-fused.md`](../../../docs/upstream/dotc-drop-outer-accessors-fused.md).

## 4. scalac: asking about the future early

scalac cannot fuse, but its info transformers are lazy, and a phase travel forward (`exitingErasure`, `exitingFlatten`) runs them before the tree transformers of the phases in between. If info transformers were pure functions of their input, and tree transformers never mutated what an info transformer had already produced, then *when* an info is first asked would not matter. [`Eager2.scala`](../probes/phases/Eager2.scala) tests that. A phase right after pickler asks every class's info, and its declarations' infos, at a later phase, and the output is compared byte for byte with a normal compile.

Over scala/scala's `test/files/run` (2.13.18, forcing at flatten): of 1431 files that compile normally, 228 are byte-identical, 1101 differ, and 102 crash. Forcing at erasure changes nothing in the small subjects. The three outcomes are three kinds of state:

* **Guarded: crashes.** `Symbol.updateInfo` asserts that the info being replaced is the latest version (`assertion failed: (21,19)`). LambdaLift's `addFreeParams` updates a constructor's info at its own phase, which fails once a flatten-phase version exists. Fails loudly: 97 of the 102.
* **Unguarded scopes: silent differences.** Flatten's info transformer copied the class's scope early, and LambdaLift and Delambdafy then entered lifted methods into the older version. The backend's `ScalaInlineInfo`, built from the late scope, lacks them (the lost update of [`copy_before_entry`](../../scala-types/ScalaTypes/Scopes.lean#L179)). Members that Constructors unlinks from the older version survive in the copy: an `$outer` field, an outer accessor.
* **Unguarded caches: wrong names.** Two names are memoized at their first read: `ClassSymbol.flattenedName` (from `rawowner` and `rawname`) and `javaBinaryNameString` (from `fullName('/')`). LambdaLift later re-owns and renames a local class. Asking for the flat name before then, which is exactly what Zinc's `ClassName.flatname` does, emits `m$E.class`, named after the enclosing method, for `class E` local to `C.m`. Asking `javaBinaryNameString` before flatten emits `p/A/Inner.class`. Zinc is safe because its API phase skips local classes (a filter again). Nothing in scalac asks early, but a plugin or macro may ([`flatname_early`](../../scala-types/ScalaTypes/Scopes.lean#L235), [`scalac-name-caches-phase-travel.md`](../../../docs/upstream/scalac-name-caches-phase-travel.md)).

The distinction behind all three is between the phase a question is *about* (`phase`, set by phase travel) and the phase the run has *reached* (`globalPhase`). A cache, a copy or an info version is safe to keep only once the run has passed the last phase that could change its inputs. Every version store in scalac is keyed on the first, and only `updateInfo` checks the second.

## 5. What this says about compiler design

A phase list reads like a function composition. It is really a set of contracts about time. Each contract says when an object may be mutated, by whom, and who may have read it already. The compilers keep those contracts in comments ("No phases that rely on scopes should be here", "Repair scopes rendered invalid by moving definitions in prior phases of the group", "must not alter `decls` directly", "This breaks type history") and in assertions that fire only on unusual programs. None of them is checked. `-Ycheck` re-typechecks trees after a phase. It does not compare a phase's view of a scope with what that phase was entitled to see, and it does not run a group unfused.

The models give the contracts a shape. For scopes, the condition is local and checkable: every entry's target version starts at its visibility phase. For fusion, it is a commutation condition between pairs of miniphases. The measured differences are each a pair that does not commute, and the compiler is correct only for the order it happens to run them in. That is the same lesson as [Track L](track-l.md)'s order sensitivity, one level down. There, a question asked during a cycle gets an answer that depends on what was forced first. Here, a question asked during a traversal gets an answer that depends on which other phases have already touched the node, the symbol or the scope.

Databases have a name for the distinction §4 ends on. A **bitemporal** store records two times per fact: *valid time*, when the fact is true in the modelled world, and *transaction time*, when the store learned it. A compiler's symbol table is a store about phases. The phase a question is about (`atPhase`, `exitingPhase`) is valid time. The phase the run has reached (`globalPhase`, or in dotc the progress of the current group) is transaction time. dotc's denotations and scalac's `TypeHistory` version facts by valid time only, and neither records when a version was written. So a read about phase 20 made at phase 5 and a read about phase 20 made at phase 25 look the same to the store, though only the second can be trusted. Every hazard in this note is a read whose valid time is ahead of its transaction time:

* a scope copy taken early ([scala/scala3#440](https://github.com/scala/scala3/issues/440));
* a name memoized early (§4);
* a miniphase seeing its group's end-of-group infos (§3);
* a phase whose entries leak into versions read about earlier phases (§2, the mirror image: transaction time ahead of valid time, written into the past).

A store that kept both times could check each read, as `updateInfo` checks each write. A compiler that cannot afford that has to keep its readers in step with its writers by discipline, which is what the comments quoted above are for.

Two checks would turn the comments into tests:

* run each phase group unfused in CI over the test suite, and compare output bytes (this track's probe, about 15 minutes over `tests/run`);
* after a run, compare each class's declarations at each phase with what was recorded during the run (this track's `Scopes2`/`Scopes3`), and fail on a difference the phase did not declare.

## Recipes

```bash
# scalac: scope versions and late answers (classpath from coursier)
java -cp "$(cs fetch --classpath org.scala-lang:scala-compiler:2.13.18):out" Scopes2 [-no-specialization] subject.scala
# dotc: fused vs unfused over a corpus
java -cp "$(cs fetch --classpath org.scala-lang:scala3-compiler_3:3.9.0):out" dotty.tools.dotc.phasesprobe.Fusion3 tests/run/*.scala
python3 fusion_classify.py fusion-output.txt
```

## Future work

* Run `Fusion3` over the rest of `tests/pos` and with `-Ycheck:all`, and split one group at a time to attribute each difference to a pair of miniphases.
* List scalac's own forward phase travels during each phase (specialization, refchecks' erasure checks, the backend) and run `Eager2` with each one's target phase, to see which are safe by luck.
* Lean: `start`-based visibility for removals (`MoveStatics`) as a theorem, not only a witness; the pre-pass and group-end hazards in [`Fusion.lean`](../../scala-types/ScalaTypes/Fusion.lean).
* Lazy-val field names are numbered per name (`b$lzy1`; adding other lazy vals, in the class or a trait, does not shift them), so only a repeated name, as with an overriding lazy val, depends on traversal order (`z1$lzy2` vs `z2$lzy1` in `tests/run/lazy-traits.scala`). They are serialized field names; check whether a repeated name can arise in a `Serializable` class.
