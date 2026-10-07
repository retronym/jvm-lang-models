import AsSeenFrom.Model
import AsSeenFrom.Scalac
import AsSeenFrom.Chain
import AsSeenFrom.IntelliJ
import AsSeenFrom.Cases

/-!
# asSeenFrom, formalized

When does the IntelliJ Scala plugin's chain of substitutor links compute the same member
type as scalac's single `asSeenFrom`? Read in order:

* `Model`: the objects (classes, types, base-type facts);
* `Scalac`: scalac's walk, the reference semantics;
* `Chain`: a chain of links is one `asSeenFrom`, and the conditions a runtime check can
  assert on a chain to make it the intended one;
* `IntelliJ`: the plugin's walk, and where it agrees with scalac's;
* `Cases`: three cases from scala/scala, decided by computation.

See `README.md` for the motivation and the map from theorems to the plugin's checks.
-/
