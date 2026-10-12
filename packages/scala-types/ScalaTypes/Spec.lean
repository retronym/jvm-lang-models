import ScalaTypes.AsSeenFrom

/-!
# `ScalaTypes`: the specification at a glance

Scala's types as scalac computes them: `asSeenFrom` once for any type language with substitutable
leaves, resolution over interfaces (linearization, signature groups, the member a selection runs),
and membership and overriding (`Scala.Members`).

* `AsSeenFrom.compose`: two `asSeenFrom` maps in sequence are one, from the first prefix as seen by
  the second.
* `AsSeenFrom.chain_is_single`: a whole chain of them is one `asSeenFrom`.

Membership is calibrated against scalac 2.12, 2.13 and dotc 3.9 on 4,704 hierarchies, rejected
programs included.
-/

-- Each name below must exist: the build fails if a result this page states is renamed or removed.
example := @AsSeenFrom.compose
example := @AsSeenFrom.chain_is_single
