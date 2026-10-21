# `ScalaTypes`

Scala's types as scalac computes them: `asSeenFrom` once for any type language with substitutable leaves (`compose`, `chain_is_single`), a typed Scala subset, desugaring of case classes, resolution over interfaces (linearization, signature groups, the member a selection runs), and membership and overriding (refchecks) as a `Task`. Shared by `scala` (lowering), `intellij` (the plugin's substitutor chains) and, later, the Zinc instances. No Mathlib.

**Start here.** [`ScalaTypes/AsSeenFrom.lean`](ScalaTypes/AsSeenFrom.lean), then [`ScalaTypes/Resolve.lean`](ScalaTypes/Resolve.lean), [`ScalaTypes/Fine.lean`](ScalaTypes/Fine.lean) and [`ScalaTypes/Members.lean`](ScalaTypes/Members.lean).

**Calibration.** `Members` against scalac's and dotc's override errors, including rejected programs ([`../scala/probes/members.py`](../scala/probes/members.py)); `asSeenFrom` through the IntelliJ TCK.

**Gaps.** Type members, `var`, `protected` and qualified access, `abstract override` ([`docs/roadmap.md`](../../docs/roadmap.md) at the repository root).

**Track T** (type soundness by oracle): the compilers' acceptance of programs over type members, stable paths and `null`, against what runs. Design: [`docs/track-t.md`](docs/track-t.md).

**Track LUB** (joins): how scalac and dotc join types when inferring, the laws that hold and the order dependence that does not, calibrated by [`probes/lub`](probes/lub/lub.py). Write-up: [`docs/track-lub.md`](docs/track-lub.md).

## Files

| File | Contents |
|---|---|
| [`ScalaTypes/Syntax.lean`](ScalaTypes/Syntax.lean) | A typed Scala subset, as the back end sees it |
| [`ScalaTypes/AsSeenFrom.lean`](ScalaTypes/AsSeenFrom.lean) | `asSeenFrom`, once, for any type language: `compose`, `chain_is_single` |
| [`ScalaTypes/Desugar.lean`](ScalaTypes/Desugar.lean) | Case classes and case objects desugared onto a library prelude |
| [`ScalaTypes/Members.lean`](ScalaTypes/Members.lean) | Membership and overriding (refchecks) as a `Task` |
| [`ScalaTypes/Resolve.lean`](ScalaTypes/Resolve.lean) | Resolution over interfaces as a `Task`: linearization (once, over declarations or headers), `seenFrom`, the members a name selects, signature groups, `winner` |
| [`ScalaTypes/Fine.lean`](ScalaTypes/Fine.lean) | The walk over headers and `member` queries is the walk over declarations ([`lookupH_eq`](ScalaTypes/Fine.lean#L240)), and asks only those queries ([`asks_lookupH`](ScalaTypes/Fine.lean#L502)) |
| [`ScalaTypes/Laziness.lean`](ScalaTypes/Laziness.lean) | Track L: true and spurious cycles in the shapes scalac and dotc have (a parent reading the class's own member under scalac's and dotc's bundlings, a consumer of every member's signature, inherited result types under the SLS and under the compilers' rule), and phase-indexed facts versioned or overwritten; Track I: scalac's implicit search under `forcePeek`, full taint and IntelliJ's rule ([`implicitSkip_memoizes_wrong`](ScalaTypes/Laziness.lean#L268), [`implicitSkip_taint_rejects`](ScalaTypes/Laziness.lean#L275), [`implicitSkip_psi_ambiguous`](ScalaTypes/Laziness.lean#L284)) |
| [`ScalaTypes/ToyNamer.lean`](ScalaTypes/ToyNamer.lean) | Track I meets Track L: the namer of the toy language of [`packages/scala/probes/interrupt`](../scala/probes/interrupt) as rules over `Query.Lazy`, under three bundlings (`fine`, `scalac`, `dotc`); Scala 3's `export` added, so that Track L's L2 and L9 are theorems by `decide`, with full taint repairing L9's answer |
| [`ScalaTypes/Lub.lean`](ScalaTypes/Lub.lean) | Track LUB: scalac's join (base type sequences in `isLess` order, `elimSub`, spanning types) and dotc's (`orDominator`, `widenInferred`, `erasedLub`) over a class hierarchy; commutativity and upper bounds proved, the order and associativity failures as witnesses |
| [`ScalaTypes/Scopes.lean`](ScalaTypes/Scopes.lean) | Track P: a class's scope versions across phases; an entry is visible after the run from the start of the version it landed in, so late answers equal the intended ones iff each entry lands where it should become visible ([`late_eq_truth_iff`](ScalaTypes/Scopes.lean#L55)); LambdaLift's and Mixin's entries in scalac, `MoveStatics` in dotc, and lazy copies that lose an entry as witnesses |
| [`ScalaTypes/Fusion.lean`](ScalaTypes/Fusion.lean) | Track P: dotc's MegaPhase fusion against running miniphases one after the other; transparent when the earlier phase only relabels ([`fused_eq_seq_of_relabel`](ScalaTypes/Fusion.lean#L79)), and a witness for each way out (reading a child, creating a subtree, `transformFollowingDeep`) |
| [`ScalaTypes/LubArgs.lean`](ScalaTypes/LubArgs.lean) | Track LUB with type arguments: variance, F-bounds, `mergePrefixAndArgs` and `lubDepth`, dotc's `lubArgs`, bounds checks; LUB2, LUB3 and LUB6 as witnesses, and a two-part fix for scalac checked on the world |
| [`ScalaTypes/Paths.lean`](ScalaTypes/Paths.lean), [`ScalaTypes/PathsOracle.lean`](ScalaTypes/PathsOracle.lean) | Track T: type members, stable paths and `null`; scalac's and dotc's checks as a `Task`, calibrated on 2,430 programs per setting ([`calibrated`](ScalaTypes/PathsOracle.lean)), and the accepted programs that throw a `ClassCastException` named ([`accepted_sound_except`](ScalaTypes/PathsOracle.lean#L68)) |
