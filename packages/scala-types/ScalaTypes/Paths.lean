import ScalaTypes.Fine
/-!
# Track T: type members, stable paths and `null`, as the compilers check them

The first space of Track T (`packages/scala-types/docs/track-t.md`): two traits with a bounded type
member `L`, a stable path of their intersection, and a dependent pair of methods that push an `Int`
into `L` and take it out at another type. The model decides whether each compiler setting *accepts*
a program; what it does when run is the oracle's (`packages/scala/probes/soundness.py`), never the
model's. `ScalaTypes.PathsOracle` holds the oracle's verdicts and the theorems relating them.

The checks, in the order the compilers meet them in a program's source:

* scalac: each trait's bounds are well formed (`lo <: hi`); dotc does not check this at the
  declaration, only where the type is realized (below);
* the path's definition: with explicit nulls `null` is not an `A & B`; dotc rejects `new A & B` whose
  members have conflicting bounds (`Checking.checkRealizableBounds`);
* the bodies: `x: Int` conforms to `L` as `up`'s view sees it (its lower bounds), and `L` as
  `down`'s view sees it conforms to the result (its upper bounds);
* after the typer: dotc rejects a type selection written on a `lazy val` whose type has conflicting
  bounds (`Checking.checkRealizable`, from `PostTyper`); scalac rejects a type member overriding
  another with bounds outside the overridden's (`RefChecks`), which `new A with B {}` does.

How a type sees `L`: through one trait, its bounds; through the intersection, Scala 3 takes the
union of the lower bounds and the intersection of the upper bounds, while Scala 2 takes the last
parent's member (a compound type's member is the one its linearization finds first). Both read
the traits by `decl` queries (`boundsOf`).
-/

open Query

namespace Scala.Paths

/-- The compiler settings: scalac 2.12 and 2.13; dotc 3.9 as is, with `-source future`, and with
`-Yexplicit-nulls`. -/
inductive Setting | s212 | s213 | s3 | s3future | s3nulls
  deriving DecidableEq, Repr

def Setting.all : List Setting := [.s212, .s213, .s3, .s3future, .s3nulls]

def Setting.scala2 : Setting → Bool
  | .s212 | .s213 => true
  | _ => false

/-- A type member as a type sees it: lower bounds (their union) and upper bounds (their
intersection). -/
structure Bounds where
  lo : List Ty
  hi : List Ty
  deriving DecidableEq, Repr

/-- Conformance on the space's types: `Nothing`, `Int`, `String`, `Any`.

Spec: cites SLS §3.5.2 -/
def conforms : Ty → Ty → Bool
  | .nothing, _ => true
  | _, .any => true
  | t, u => t == u

/-- `t <: L`: `t` conforms to one of the lower bounds. -/
def Bounds.admits (b : Bounds) (t : Ty) : Bool := b.lo.any (conforms t ·)

/-- `L <: u`: one of the upper bounds conforms to `u`. -/
def Bounds.within (b : Bounds) (u : Ty) : Bool := u == .any || b.hi.any (conforms · u)

/-- The union of the lower bounds conforms to the intersection of the upper bounds. -/
def Bounds.consistent (b : Bounds) : Bool := b.lo.all fun l => b.hi.all fun h => conforms l h

def _root_.Scala.TMem.bounds (m : TMem) : Bounds := ⟨[m.lo], [m.hi]⟩

def _root_.Scala.Decl.tmem (d : Decl) (n : String) : Option TMem := d.tmems.find? (·.name == n)

/-- Member `n` of the intersection of `ds`, in order.

Spec: cites SLS §3.2.7
Spec: unspecified SLS §3.2.7: the bounds of an abstract type member of a compound type `A with B`
whose parents both declare it. scalac takes the last parent's; dotc, for `A & B`, the union of the
lower bounds and the intersection of the upper ones (the Scala 3 reference on intersection types).
Calibrated on 2,430 programs per setting (`PathsOracle.calibrated`). -/
def interBounds (s : Setting) (ds : List Decl) (n : String) : Bounds :=
  let ms := ds.filterMap (·.tmem n)
  if s.scala2 then (ms.getLast?.map TMem.bounds).getD ⟨[.nothing], [.any]⟩
  else ⟨ms.map (·.lo), ms.map (·.hi)⟩

/-- Member `n` of a path whose type is the intersection of the definitions `ps`, read by `decl`
queries. -/
def boundsOf (s : Setting) (ps : List String) (n : String) : M Bounds := do
  let ds ← ps.mapM need
  pure (interBounds s ds n)

/-! ## The first space -/

/-- The path: a `val` initialised to `null`, a `lazy val` initialised to `???`, a method parameter
passed `null`, a field of an object (`h.f`) initialised to `null`, or `new A with B {}`. -/
inductive PathKind | valNull | lazyVal | param | field | new_
  deriving DecidableEq, Repr

def PathKind.nullValued : PathKind → Bool
  | .valNull | .param | .field => true
  | _ => false

/-- How the methods see `L`: `up` through `A` and `down` through `B`; the other way round; or both
through the path itself (`p.L`). -/
inductive View | two | swapped | inter
  deriving DecidableEq, Repr

structure Prog where
  loA : Ty
  hiA : Ty
  loB : Ty
  hiB : Ty
  path : PathKind
  view : View
  /-- What `down` returns: `String` (where a wrong value is caught by a cast) or `Any`. -/
  out : Ty
  deriving DecidableEq, Repr

def trait (n : String) (lo hi : Ty) : Src :=
  { name := n, cls := some { name := n, kind := .trt, tmems := [{ name := "L", lo := lo, hi := hi }] } }

def Prog.program (p : Prog) : Program := [trait "A" p.loA p.hiA, trait "B" p.loB p.hiB]

def los : List Ty := [.nothing, .int, .str]
def his : List Ty := [.any, .int, .str]

def space : List Prog := do
  let loA ← los; let hiA ← his; let loB ← los; let hiB ← his
  let path ← [PathKind.valNull, .lazyVal, .param, .field, .new_]
  let view ← [View.two, .swapped, .inter]
  let out ← [Ty.str, .any]
  pure ⟨loA, hiA, loB, hiB, path, view, out⟩

/-! ## The checks -/

/-- A program's verdict: accepted, or the first error by kind. -/
inductive Verdict
  | accept
  /-- A trait's lower bound does not conform to its upper bound. -/
  | wellFormed
  /-- Explicit nulls: `null` is not an `A & B`. -/
  | nullPath
  /-- dotc: `new A & B` with a member of conflicting bounds. -/
  | instantiate
  /-- A body does not conform (type mismatch). -/
  | mismatch
  /-- dotc: a type selection on a `lazy val` whose type has conflicting bounds is not a legal path. -/
  | notPath
  /-- scalac: `B`'s `L` overrides `A`'s with bounds outside them. -/
  | override
  deriving DecidableEq, Repr

/-- scalac's check of an abstract type member overriding another: the overriding bounds lie within
the overridden ones.

Spec: cites SLS §5.1.4 -/
def overrideOk (high low : Bounds) : Bool :=
  high.lo.all (fun l => low.lo.all (conforms l ·)) && low.hi.all (fun h => high.hi.all (conforms h ·))

/-- The compiler's check, as a task over the program's declarations.

Spec: cites SLS §4.3, SLS §5.1.4
Spec: contradicts SLS §4.3 / dotc 3.9.0: "It is a compile-time error if L does not conform to U",
but dotc accepts `trait B { type L >: Int <: String }` and rejects it only where the type is
realized; scalac rejects the declaration (`PathsOracle.calibrated`). With a `null` path such a
program throws a cast-free `ClassCastException` (`PathsOracle.accepted_sound_except`). -/
def check (s : Setting) (p : Prog) : M Verdict := do
  let a ← boundsOf s ["A"] "L"
  let b ← boundsOf s ["B"] "L"
  let ab ← boundsOf s ["A", "B"] "L"
  if s.scala2 && (!a.consistent || !b.consistent) then return .wellFormed
  if s == .s3nulls && (p.path == .valNull || p.path == .field) then return .nullPath
  if !s.scala2 && p.path == .new_ && !ab.consistent then return .instantiate
  let (vu, vd) := match p.view with
    | .two => (a, b)
    | .swapped => (b, a)
    | .inter => (ab, ab)
  if !vu.admits .int || !vd.within p.out then return .mismatch
  if s == .s3nulls && p.path == .param then return .nullPath
  if !s.scala2 && p.path == .lazyVal && p.view == .inter && !ab.consistent then return .notPath
  if s.scala2 && p.path == .new_ && !overrideOk a b then return .override
  pure .accept

def verdict (s : Setting) (p : Prog) : Verdict :=
  match ex p.program.env (check s p) with
  | .ok v => v
  | .error _ => .wellFormed

def accepts (s : Setting) (p : Prog) : Bool := verdict s p == .accept

/-! ## As Scala source

Written with `PKG` for the package and `AND` for the intersection operator, as the probe's
catalogue is (`packages/scala/probes/soundness.py`). -/

def bound (lo hi : Ty) : String :=
  (if lo == .nothing then "" else s!" >: {lo.show}") ++ (if hi == .any then "" else s!" <: {hi.show}")

def Prog.source (p : Prog) : String :=
  let o := p.out.show
  let path := match p.path with | .field => "h.f" | _ => "p"
  let decl := match p.path with
    | .valNull => ["  val p: A AND B = null"]
    | .lazyVal => ["  lazy val p: A AND B = ???"]
    | .field => ["  class Holder { val f: A AND B = null }", "  val h = new Holder"]
    | .new_ => ["  val p = new A with B {}"]
    | .param => []
  let (defs, expr) := match p.view, p.path with
    | .inter, .param =>
      ([s!"  def go(p: A AND B): {o} = \{ val l: p.L = 1; val r: {o} = l; r }"], "go(null)")
    | .inter, _ =>
      ([s!"  def up(x: Int): {path}.L = x", s!"  def down(l: {path}.L): {o} = l"], "down(up(1))")
    | v, pk =>
      let (t1, t2) := if v == View.two then ("A", "B") else ("B", "A")
      let ds := [s!"  def up(a: {t1})(x: Int): a.L = x", s!"  def down(b: {t2})(l: b.L): {o} = l"]
      if pk == PathKind.param then (ds ++ [s!"  def go(p: A AND B): {o} = down(p)(up(p)(1))"], "go(null)")
      else (ds, s!"down({path})(up({path})(1))")
  let use := if p.out == Ty.str then "s.length" else "s"
  "\n".intercalate (["package PKG", "object Main {",
    s!"  trait A \{ type L{bound p.loA p.hiA} }", s!"  trait B \{ type L{bound p.loB p.hiB} }"] ++
    decl ++ defs ++ ["  def main(args: Array[String]): Unit = {", s!"    val s: {o} = {expr}",
    s!"    println({use})", "  }", "}", ""])

example : space.length = 2430 := by decide +kernel

end Scala.Paths
