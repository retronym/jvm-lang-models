# `ScalaTypes`

Scala's types as scalac computes them: `asSeenFrom` once for any type language with substitutable leaves (`compose`, `chain_is_single`), a typed Scala subset, desugaring of case classes, resolution over interfaces (linearization, signature groups, the member a selection runs), and membership and overriding (refchecks) as a `Task`. Shared by `scala` (lowering), `intellij` (the plugin's substitutor chains) and, later, the Zinc instances. No Mathlib.

**Start here.** `ScalaTypes/AsSeenFrom.lean`, then `ScalaTypes/Resolve.lean` and `ScalaTypes/Members.lean`.

**Calibration.** `Members` against scalac's and dotc's override errors, including rejected programs (`../scala/probes/members.py`); `asSeenFrom` through the IntelliJ TCK.

**Gaps.** Type members, `var`, `protected` and qualified access, `abstract override` (`docs/ROADMAP.md` at the repository root).

## Files

| File | Contents |
|---|---|
| `ScalaTypes/Syntax.lean` | A typed Scala subset, as the back end sees it |
| `ScalaTypes/AsSeenFrom.lean` | `asSeenFrom`, once, for any type language: `compose`, `chain_is_single` |
| `ScalaTypes/Desugar.lean` | Case classes and case objects desugared onto a library prelude |
| `ScalaTypes/Members.lean` | Membership and overriding (refchecks) as a `Task` |
| `ScalaTypes/Resolve.lean` | Resolution over interfaces as a `Task`: linearization, `seenFrom`, the members a name selects, signature groups, `winner` |
