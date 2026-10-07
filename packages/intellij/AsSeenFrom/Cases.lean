import AsSeenFrom.Chain
import AsSeenFrom.IntelliJ

/-!
# Two cases from scala/scala, as checked computations

Each case is a small world, a table of `bpre` and `hasBase` facts cut down from
scala/scala b4ad4458da, and a few equations closed by `decide`. The worlds are tables,
not derived from a class table, so each example proves "under these base-type facts,
the walks compute this". Case B shows a mis-anchored chain; case A shows the plugin's
fallback rewriting where scalac's walk stops.
-/

namespace Cases
open Scalac Chain

/-! ## Case (b): `patmat/MatchWarnings.scala` — a link anchored before the view moved

    trait PatternMatching { … trait MatchMonadInterface { val typer: Typer } … }   -- pm, mmi
    trait MatchTranslation { self: PatternMatching =>
      trait MatchTranslator extends … with TreeMakerWarnings { … } }               -- mt, mtr
    trait MatchWarnings { self: PatternMatching =>
      trait TreeMakerWarnings { self: MatchTranslator => import typer.context } }   -- mw, tmw

`info(typer)` mentions `PatternMatching.this`: it is the `Typer` of this universe.
Resolving `typer` on `TreeMakerWarnings.this` finds it through the self type
`MatchTranslator`, so the plugin's chain is `sig_MatchTranslator >> use`, where `use`
rewrites onto `TreeMakerWarnings.this`. The question is the anchor of `use`.
`sig_MatchTranslator` has already moved the type into `MatchTranslator`'s view, so the
well-anchored choice is `MatchTranslator`. The plugin used to anchor at the declaring
class, `MatchMonadInterface`, whose enclosing classes never reach `MatchTranslator`.
-/
namespace B

def pm  : Class := [0]
def mmi : Class := [1, 0]
def mt  : Class := [2]
def mtr : Class := [3, 2]
def mw  : Class := [4]
def tmw : Class := [5, 4]

/-- Base-type prefixes read off the source: `MatchTranslator.this baseType MatchMonadInterface`
has prefix `MatchTranslation.this` (the self type `PatternMatching` is spelled through the
enclosing trait); `TreeMakerWarnings.this baseType MatchTranslator` has prefix
`MatchWarnings.this`; and for either this-prefix, `baseType PatternMatching` has the
package prefix, which we model as an unrelated this-leaf that is never rewritten. -/
def bpre : Ty → Class → Ty
  | .this [3, 2], [1, 0] => .this mt      -- MatchTranslator.this baseType MMI → MatchTranslation.this
  | .this [5, 4], [3, 2] => .this mw      -- TreeMakerWarnings.this baseType MatchTranslator → MatchWarnings.this
  | .this [5, 4], [1, 0] => .this mw      -- TreeMakerWarnings.this baseType MMI → MatchWarnings.this (via the self type)
  | p, _ => p

def hasBase : Ty → Class → Bool
  | .this [3, 2], [1, 0] => true
  | .this [5, 4], [3, 2] => true
  | .this [5, 4], [1, 0] => true
  | .this [2],    [0]    => true   -- MatchTranslation.this : PatternMatching (self type)
  | .this [4],    [0]    => true   -- MatchWarnings.this : PatternMatching (self type)
  | .this [4],    [2]    => true   -- … and so a MatchTranslation
  | p, c => p == .this c

def W : World := ⟨bpre, hasBase⟩

/-- `info(typer)`: `PatternMatching.this.Typer`. -/
def infoTyper : Ty := .sel (.this pm) 42

/-- Signature substitutor of `MatchTranslator`: `typer` in `MatchTranslator`'s view. -/
def sig : Link := ⟨.this mtr, mmi⟩

/-- The use-site link, anchored at the declaring class: not well anchored. -/
def linkAtOwner : Link := ⟨.this tmw, mmi⟩
/-- The same link anchored at `MatchTranslator`, the class whose view the type is now
in: well anchored. -/
def linkAtView  : Link := ⟨.this tmw, mtr⟩

/-- What scalac computes: `TreeMakerWarnings.this.memberType(typer)`. -/
def scalac : Ty := asf W (.this tmw) mmi infoTyper

example : scalac = .sel (.this mw) 42 := by decide
example : applyChain W [sig, linkAtView]  infoTyper = scalac := by decide
example : applyChain W [sig, linkAtOwner] infoTyper = .sel (.this mt) 42 := by decide
example : applyChain W [sig, linkAtOwner] infoTyper ≠ scalac := by decide

/-- `compose` names the prefix each chain views from. Anchored at
`MatchMonadInterface`, the walk never reaches `MatchTranslator` and leaves
`MatchTranslator.this` unchanged, so the chain is `typer` seen from `MatchTranslator.this`,
the wrong prefix. Anchored at `MatchTranslator`, the walk rewrites `MatchTranslator.this`
to `TreeMakerWarnings.this` (the self type makes them one instance), the right prefix.
**Both chains are one `asSeenFrom`; only the well-anchored one is scalac's.** -/
example : asf W (.this tmw) mmi (.this mtr) = .this mtr := by decide
example : asf W (.this tmw) mtr (.this mtr) = .this tmw := by decide
example : applyChain W [sig, linkAtOwner] infoTyper = asf W (.this mtr) mmi infoTyper := by decide
example : applyChain W [sig, linkAtView]  infoTyper = asf W (.this tmw) mmi infoTyper := by decide

end B

/-! ## Case (a): `reflect/internal/Importers.scala` — the fallback narrows by inheritance

    trait Importers { to: SymbolTable =>                                  -- im
      abstract class StandardImporter { val from: SymbolTable; … } }      -- si
    abstract class SymbolTable extends … with Importers                   -- st

The link `` `this` -> from.type asSeenFrom StandardImporter `` fires on `Importers.this`.
`from` is a `SymbolTable`, which inherits `Importers`, but it is not a
`StandardImporter`, so `from baseType StandardImporter` does not exist. scalac's walk
runs out of prefix and leaves `Importers.this` alone. The plugin's fallback sees that
`StandardImporter` is enclosed by `Importers` and that `from`'s class inherits
`Importers`, and rewrites `Importers.this` to `from`: a type of this universe becomes a
type of `from`. In the plugin this link came from `BaseProcessor.processType`, which
anchored every member of the path `from` at `from`'s own declaring class,
`StandardImporter`. Each member is now anchored at its own class, so the fallback no
longer meets this input.
-/
namespace A

def im : Class := [0]
def si : Class := [1, 0]
def st : Class := [2]

/-- The path `from`, as a selection off `StandardImporter.this`. -/
def fromPath : Ty := .sel (.this si) 7

def E : IntelliJ.Env where
  bpre    := fun p _ => p
  hasBase := fun p c => p == .this c
  inherits := fun a b => a == b || (a == st && b == im)
  clsOf := fun p => if p == fromPath then st else []

example : Scalac.thisAsSeen E.toWorld im si fromPath = .this im := by decide
example : IntelliJ.thisAsSeen E im si fromPath = fromPath := by decide

end A

end Cases
