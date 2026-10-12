import IntelliJ.Relaxations
import IntelliJ.Plugin

/-!
# `IntelliJ`: the specification at a glance

When do the IntelliJ Scala plugin's chains of substitutor links compute the same member type as
scalac's single `asSeenFrom`? Each theorem is a runtime check in the plugin.

* `Chain.compose`, `Chain.chain_is_single`: a chain of links is one `asSeenFrom`.
* `Chain.chain_is_intended`: if each link is anchored at the class of the prefix composed so far,
  that `asSeenFrom` is from the intended prefix.
* `Chain.once_is_scalac`, `Chain.selfRooted_twice_diverges`: a self-rooted link is right once and
  wrong twice.
* `IntelliJ.agrees`: the plugin's walk equals scalac's wherever its fallback does not fire.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def IntelliJ.spec : List Lean.Name :=
  [``Chain.compose,
   ``Chain.chain_is_single,
   ``Chain.chain_is_intended,
   ``Chain.once_is_scalac,
   ``Chain.selfRooted_twice_diverges,
   ``IntelliJ.agrees]
