import AsSeenFrom.Model
import AsSeenFrom.Scalac
import AsSeenFrom.Shared
import AsSeenFrom.Port
import AsSeenFrom.Chain
import AsSeenFrom.Relaxations
import AsSeenFrom.IntelliJ
import AsSeenFrom.Cases

/-!
# asSeenFrom, formalized

When does the IntelliJ Scala plugin's chain of substitutor links compute the same member
type as scalac's single `asSeenFrom`? Read in order:

* `Model`: the objects (classes, types, base-type facts);
* `Scalac`: scalac's walk, the reference semantics;
* `Shared`, `Port`: the same walk as stated once for any type language in retronym/talks, and
  the proof that `Scalac.asf` is that map;
* `Chain`: a chain of links is one `asSeenFrom`, and the conditions a runtime check can
  assert on a chain to make it the intended one;
* `Relaxations`: links that are not idempotent and still right, the shapes a relaxed
  check A1 admits;
* `IntelliJ`: the plugin's walk, and where it agrees with scalac's;
* `Cases`: cases from scala/scala, decided by computation.

See `README.md` for the motivation and the map from theorems to the plugin's checks.
-/
