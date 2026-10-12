import Zinc.Loop.PingPong
import Zinc.Loop.Cycles
import Zinc.Loop.Files
import Zinc.Bridges.HierSound
import Zinc.Bridges.Flat
import Zinc.Features.Erasure
import Zinc.Features.ImplicitScope
import Zinc.Features.Sam

/-!
# `Zinc`: the specification at a glance

Zinc as instances of `IncComp`. Each feature instance states today's bridge as keys, each bug
family as a failed obligation with a witness, and the fix as keys with the obligations proved for
every program. `Zinc.Features.Sam` is the template for a new one.

**The loop.**

* `Zinc.PingPong.zinc_diverges`: without `transitiveStep`, Zinc's loop does not stop on three
  classes whose inferred types read each other, for any fuel.
* `Zinc.Cycles.zinc_ne_clean`: with mutually inferred types the loop can stop at a result that is
  not the clean build's; `Zinc.Cycles.annotated_eq_clean`: with every member annotated it cannot.
* `IncComp.XCompiler.zinc_sound_charged`: the loop over files, with imports charged to one class
  of a file, is sound.

**Bridges and their variants.** `Zinc.Hier.D_obligations`, `Zinc.Hier.W_obligations`,
`Zinc.Hier.Mk_obligations`: declarations with a walk, materialised members and Merkle hashes all
meet the obligations. `Zinc.Flat.flat_sound`: the Merkle PoC's descendant rules are sound.

**Features.** `Zinc.Erasure.Er_obligations` (erasure through inheritance, as declared, with the
class kind in the class-name hash); `Zinc.ImplicitScope.is_sound` (implicit scope through an
ancestor's companion across subprojects, sbt/zinc#1845's summary folded into the API hash).
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def Zinc.spec : List Lean.Name :=
  [``Zinc.PingPong.zinc_diverges,
   ``Zinc.Cycles.zinc_ne_clean,
   ``Zinc.Cycles.annotated_eq_clean,
   ``IncComp.XCompiler.zinc_sound_charged,
   ``Zinc.Hier.D_obligations,
   ``Zinc.Hier.W_obligations,
   ``Zinc.Hier.Mk_obligations,
   ``Zinc.Flat.flat_sound,
   ``Zinc.Erasure.Er_obligations,
   ``Zinc.ImplicitScope.is_sound]
