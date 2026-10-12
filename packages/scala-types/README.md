# `ScalaTypes`

Scala's types as scalac computes them: `asSeenFrom` once for any type language with substitutable leaves (`compose`, `chain_is_single`), a typed Scala subset, desugaring of case classes, resolution over interfaces (linearization, signature groups, the member a selection runs), and membership and overriding (refchecks) as a `Task`. Shared by `scala` (lowering), `intellij` (the plugin's substitutor chains) and, later, the Zinc instances. No Mathlib.

**Start here.** [`ScalaTypes/AsSeenFrom.lean`](ScalaTypes/AsSeenFrom.lean), then [`ScalaTypes/Resolve.lean`](ScalaTypes/Resolve.lean), [`ScalaTypes/Fine.lean`](ScalaTypes/Fine.lean) and [`ScalaTypes/Members.lean`](ScalaTypes/Members.lean).

**Calibration.** `Members` against scalac's and dotc's override errors, including rejected programs ([`../scala/probes/members.py`](../scala/probes/members.py)); `asSeenFrom` through the IntelliJ TCK.

**Gaps.** Type members, `var`, `protected` and qualified access, `abstract override` ([`docs/roadmap.md`](../../docs/roadmap.md) at the repository root).

**Track T** (type soundness by oracle): the compilers' acceptance of programs over type members, stable paths and `null`, against what runs. Design: [`docs/track-t.md`](docs/track-t.md).

## Files

| File | Contents |
|---|---|
| [`ScalaTypes/Syntax.lean`](ScalaTypes/Syntax.lean) | A typed Scala subset, as the back end sees it |
| [`ScalaTypes/AsSeenFrom.lean`](ScalaTypes/AsSeenFrom.lean) | `asSeenFrom`, once, for any type language: `compose`, `chain_is_single` |
| [`ScalaTypes/Desugar.lean`](ScalaTypes/Desugar.lean) | Case classes and case objects desugared onto a library prelude |
| [`ScalaTypes/Members.lean`](ScalaTypes/Members.lean) | Membership and overriding (refchecks) as a `Task` |
| [`ScalaTypes/Resolve.lean`](ScalaTypes/Resolve.lean) | Resolution over interfaces as a `Task`: linearization (once, over declarations or headers), `seenFrom`, the members a name selects, signature groups, `winner` |
| [`ScalaTypes/Fine.lean`](ScalaTypes/Fine.lean) | The walk over headers and `member` queries is the walk over declarations ([`lookupH_eq`](ScalaTypes/Fine.lean#L240)), and asks only those queries ([`asks_lookupH`](ScalaTypes/Fine.lean#L502)) |
| [`ScalaTypes/Paths.lean`](ScalaTypes/Paths.lean), [`ScalaTypes/PathsOracle.lean`](ScalaTypes/PathsOracle.lean) | Track T: type members, stable paths and `null`; scalac's and dotc's checks as a `Task`, calibrated on 2,430 programs per setting ([`calibrated`](ScalaTypes/PathsOracle.lean)), and the accepted programs that throw a `ClassCastException` named ([`accepted_sound_except`](ScalaTypes/PathsOracle.lean#L68)) |
