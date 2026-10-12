import IntelliJ.Model
import IntelliJ.Scalac
import ScalaTypes.AsSeenFrom
import IntelliJ.Port
import IntelliJ.Chain
import IntelliJ.Relaxations
import IntelliJ.Plugin
import IntelliJ.Cases
import IntelliJ.Spec

/-!
# The IntelliJ Scala plugin's asSeenFrom, formalized

When does the IntelliJ Scala plugin's chain of substitutor links compute the same member
type as scalac's single `asSeenFrom`? Read in order:

* `Model`: the objects (classes, types, base-type facts);
* `Scalac`: scalac's walk, the reference semantics;
* `ScalaTypes.AsSeenFrom`, `Port`: the same walk as stated once for any type language in the
  `scala-types` package, and the proof that `Scalac.asf` is that map;
* `Chain`: a chain of links is one `asSeenFrom`, and the conditions a runtime check can
  assert on a chain to make it the intended one;
* `Relaxations`: links that are not idempotent and still right, the shapes a relaxed
  check A1 admits;
* `Plugin`: the plugin's walk, and where it agrees with scalac's;
* `Cases`: cases from scala/scala, decided by computation.

See `README.md` for the motivation and the map from theorems to the plugin's checks.
-/
