import AsSeenFrom.Chain
import AsSeenFrom.IntelliJ
import AsSeenFrom.Relaxations

/-!
# Two cases from scala/scala, as checked computations

Each case is a small world, a table of `bpre` and `hasBase` facts cut down from
scala/scala b4ad4458da, and a few equations closed by `decide`. The worlds are tables,
not derived from a class table, so each example proves "under these base-type facts,
the walks compute this". Case B shows a mis-anchored chain; case A shows the plugin's
fallback rewriting where scalac's walk stops; case C shows a self-rooted link, right
once and wrong twice. Cases D and E are the shapes `Relaxations` admits: a compound
self-rooted target, and a target rooted in the anchor's owner.
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

/-! ## Case (c): `ast/parser/Scanners.scala` — a self-rooted link, right once, wrong twice

    trait Scanners {                                                       -- sc
      class UnitScanner … { lazy val parensAnalyzer = new ParensAnalyzer(…)  -- us
                           def balance … }
      class ParensAnalyzer … extends UnitScanner(…) }                       -- pa

Inside `UnitScanner`, `parensAnalyzer.balance(token)` views a member that
`ParensAnalyzer` inherits from `UnitScanner` through the link
`` `this` -> UnitScanner.this.parensAnalyzer.type asSeenFrom UnitScanner ``. Its target
is rooted in `UnitScanner.this`, the very this-type it rewrites: `Chain.SelfRooted`.
Take a member type `UnitScanner.this.T`.
-/
namespace C

def sc : Class := [0]
def us : Class := [1, 0]
def pa : Class := [2, 0]

/-- The path `UnitScanner.this.parensAnalyzer`. -/
def parensAnalyzer : Ty := .sel (.this us) 7

/-- A `ParensAnalyzer` is a `UnitScanner`, and either one's base type `UnitScanner`
has prefix `Scanners.this`. -/
def bpre : Ty → Class → Ty
  | _, [1, 0] => .this sc
  | p, _      => p

def hasBase : Ty → Class → Bool
  | .sel (.this [1, 0]) 7, [1, 0] => true    -- parensAnalyzer : UnitScanner
  | p, c => p == .this c

def W : World := ⟨bpre, hasBase⟩

def link : Link := ⟨parensAnalyzer, us⟩

/-- A member type `UnitScanner.this.T`. -/
def memberT : Ty := .sel (.this us) 42

/-- scalac: the receiver's `UnitScanner.this` becomes `parensAnalyzer`; the
`UnitScanner.this` inside `parensAnalyzer` is the enclosing scanner and stays. -/
example : asf W parensAnalyzer us memberT = .sel (.sel (.this us) 7) 42 := by decide

/-- The link once is scalac's; the link twice rewrites the enclosing scanner too, giving
`UnitScanner.this.parensAnalyzer.parensAnalyzer.T`. -/
example : applyChain W [link] memberT = asf W parensAnalyzer us memberT := by decide
example : applyChain W [link, link] memberT = .sel (.sel (.sel (.this us) 7) 7) 42 := by decide
example : applyChain W [link, link] memberT ≠ asf W parensAnalyzer us memberT := by decide

/-- The link is self-rooted, so the general lemmas apply: it does not fix its target,
and so lies outside `idempotent_of_fixed`. -/
theorem selfRooted : SelfRooted W link.pre link.anchor :=
  ⟨by decide, .sel 7 .root, by decide, by decide⟩

example : asf W link.pre link.anchor link.pre ≠ link.pre :=
  selfRooted_moves_target W _ _ selfRooted

end C

/-! ## Case (d): a compound self-rooted link, and the `processType` duplicate

    trait T1 { type M3 }      -- t1

The link `T1.this -> T1 with T1.this.M3` has a compound target with a part rooted in the
very this-type it rewrites (`Relax.PartSelfRooted`). `ScProjectionType.processType` used
to apply it twice, growing `T1 with (T1 with T1.this.M3)#M3`. The package is the empty
class, so `T1` the type is `<pkg>.this.T1`.
-/
namespace D
open Relax

def t1 : Class := [1]
def T1 : Ty := .sel (.this []) 1
def target : Ty := .pair T1 (.sel (.this t1) 3)

def W : World where
  bpre    := fun _ _ => .this []
  hasBase := fun p c => p == target && c == t1 || p == .this c

def link : Link := ⟨target, t1⟩

example : applyChain W [link] (.this t1) = target := by decide
example : applyChain W [link, link] (.this t1) = .pair T1 (.sel target 3) := by decide

theorem partSelfRooted : PartSelfRooted W link.pre link.anchor :=
  ⟨by decide, .right _ (.path (.sel 3 .root)), by decide, by decide⟩

example : applyChain W [link, link] (.this t1) ≠ applyChain W [link] (.this t1) :=
  partRooted_twice_diverges W link partSelfRooted

end D

/-! ## Case (e): an outer-rooted link, fixed or not depending on the world

    trait T2 { val v12: I2; trait I2 }     -- t2, i2

The link `I2.this -> T2.this.v12.type` is rooted in `T2.this`, the owner of its anchor.
If `v12` is an `I2` of this very `T2`, `(v12 baseType I2).prefix` is `T2.this` and the
link fixes its target. If instead `val v12: other.I2` for some `val other: T2`, the
prefix is `T2.this.other`, and the link moves its target to `T2.this.other.v12`.
-/
namespace E
open Relax

def t2 : Class := [2]
def i2 : Class := [5, 2]
def v12 : Ty := .sel (.this t2) 12
def other : Ty := .sel (.this t2) 99

def hasBase : Ty → Class → Bool
  | .sel (.this [2]) 12, [5, 2] => true   -- v12 : I2
  | .sel (.this [2]) 99, [2]    => true   -- other : T2
  | p, c => p == .this c

/-- `val v12: I2`: an `I2` of this `T2`. -/
def Wsame : World := ⟨fun p c => if p == v12 && c == i2 then .this t2 else p, hasBase⟩
/-- `val v12: other.I2`: an `I2` of another `T2`. -/
def Wother : World := ⟨fun p c => if p == v12 && c == i2 then other else p, hasBase⟩

def link : Link := ⟨v12, i2⟩

theorem outerSame : OuterRooted Wsame v12 i2 t2 := ⟨by decide, .sel 12 .root, by decide⟩
theorem outerOther : OuterRooted Wother v12 i2 t2 := ⟨by decide, .sel 12 .root, by decide⟩

example : asf Wsame v12 i2 v12 = v12 :=
  (outerRooted_fixed_iff_owner Wsame v12 5 t2 outerSame).2 (by decide)
example : asf Wother v12 i2 v12 = .sel other 12 := by decide
example : applyChain Wother [link, link] (.this i2) ≠ applyChain Wother [link] (.this i2) :=
  outerRooted_twice_diverges Wother link t2 outerOther (by decide) (by decide) (by decide)

end E

end Cases
