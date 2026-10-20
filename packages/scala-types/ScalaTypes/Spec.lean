import ScalaTypes.AsSeenFrom
import ScalaTypes.Fine
import ScalaTypes.Laziness

/-!
# `ScalaTypes`: the specification at a glance

Scala's types as scalac computes them: `asSeenFrom` once for any type language with substitutable
leaves, resolution over interfaces (linearization, signature groups, the member a selection runs),
and membership and overriding (`Scala.Members`).

* `AsSeenFrom.compose`: two `asSeenFrom` maps in sequence are one, from the first prefix as seen by
  the second.
* `AsSeenFrom.chain_is_single`: a whole chain of them is one `asSeenFrom`.
* `Scala.lookupH_eq`: member lookup over headers and per-name `member` queries is member lookup over
  whole declarations, in every environment whose finer answers are projections of `decl`
  (`Scala.Consistent`, which `Scala.Program.envIn_consistent` gives for every program). Its parts:
  `Scala.lin_fine` (the linearization, class by class) and `Scala.firstHit_fine` (the first hit).
* `Scala.asks_lookupH`: that lookup asks only `header` and `member` queries.

Membership is calibrated against scalac 2.12, 2.13 and dotc 3.9 on 4,704 hierarchies, rejected
programs included.

Track L, true and spurious cycles (`ScalaTypes.Laziness`):

* `ScalaTypes.Laziness.fine5_ranked`, `ScalaTypes.Laziness.scalac5_unranked`,
  `ScalaTypes.Laziness.dotc5_ok`: `class C extends B[C#T] { type T = C }` is well-founded; scalac's
  bundling of parents and members into one class info has no ranking; dotc's `TempClassInfo`
  succeeds. A spurious cycle.
* `ScalaTypes.Laziness.slsI_ranked`, `ScalaTypes.Laziness.implI_unranked`: an overriding method's
  inferred type is well-founded under the SLS's rule and cyclic under the compilers'.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def ScalaTypes.spec : List Lean.Name :=
  [``AsSeenFrom.compose,
   ``AsSeenFrom.chain_is_single,
   ``Scala.lookupH_eq,
   ``Scala.lin_fine,
   ``Scala.firstHit_fine,
   ``Scala.Program.envIn_consistent,
   ``Scala.asks_lookupH,
   ``ScalaTypes.Laziness.fine5_ranked,
   ``ScalaTypes.Laziness.scalac5_unranked,
   ``ScalaTypes.Laziness.dotc5_ok,
   ``ScalaTypes.Laziness.slsI_ranked,
   ``ScalaTypes.Laziness.implI_unranked]
