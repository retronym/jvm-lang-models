import Zinc.Bridges.FlatRules
import Zinc.Bridges.HierShared
import ScalaTypes.Members
/-!
# `Flat`'s toy Scala, embedded in the shared Scala semantics

`Flat` extends `Hier`'s language with member kinds (`val`, `var`, `lazy val`), deferred and private
members, traits, objects, `final` and abstract classes, and runs a class's refchecks and codegen
against its ancestors. This file says what its programs mean in the shared semantics and compares,
over `FlatRules`' 216,000 programs (`lake exe exhaustive flatshared`):

* **linearization**: each class's stored linearization (`Iface.lin`), with type arguments, against
  `Scala.lin`;
* **selection**: each client's resolved type against the first member along the receiver's
  linearization, viewed from it (`Scala.hits`, `Scala.seenFrom`);
* **refchecks**: each class's errors, by kind, against `Scala.Members.errors` (scalac 2.13): an
  override (`resultType`, `stable`, `lazyMismatch`), a conflict (`conflicting`, `accidental`), an
  unimplemented abstract member (`needsAbstract`). A `final` parent is not in `Members` (scalac
  checks it in the typer), so it is left out of the comparison.

`Members` has no `var`; programs in which the trait declares one are counted apart.

Results, over the 192,000 programs without a `var` (`lake exe exhaustive flatshared [2.12|2.13|3]`):

| | 2.12 | 2.13 | 3 |
|---|---|---|---|
| linearization agrees | 192,000 | 192,000 | 192,000 |
| selections agree | 192,000 | 192,000 | 192,000 |
| each class compiles under both, or fails under both | 184,640 | 124,352 | 191,680 |
| the same errors, by kind and class | 171,392 | 103,824 | 184,064 |

`Flat`'s refchecks are closest to Scala 3's. What is left:

* **Scala 2.13 re-checks a pair a parent already has**, and reports it again in the subclass;
  `Flat`, like 2.12 and 3, checks it once (scalac's `OverridingPairs`).
* **Scala 3, 320 programs:** `trait A extends M` re-declares `m` abstract over `M`'s concrete `m`,
  `B extends A`, `C extends B with M`. dotc accepts `C`, because `M` is a direct parent; `Flat`
  lets the abstract declaration win, as javac does. Neither is the specification, under which a
  concrete definition always overrides an abstract one (`Scala.Members.concreteS3`).
* **Which errors a broken class reports** differs more than whether it compiles: `Flat` checks
  inherited conflicts only for names the class does not declare.

Checking this comparison found two gaps in the shared semantics, both fixed in `Scala.Members` and
pinned by witnesses there: an abstract member and a concrete one of an incompatible type through
different parents (both compilers reject), and Scala 3's re-abstraction by a trait.
-/

open Query

namespace Zinc.Flat.Shared

open Zinc.Hier (Cls Name Ty)
open Zinc.Hier.Shared (clsName nameStr)

def tyToScala (self : Cls) : Ty → Scala.Ty := Zinc.Hier.Shared.Ty.toScala self

def memToScala (self : Cls) (n : Name) (mm : Mem) : Scala.Mem :=
  { name := nameStr n, res := tyToScala self mm.ty, abs := mm.deferred, priv := mm.priv,
    isVal := mm.mod == .val || mm.mod == .lzy, lzy := mm.mod == .lzy, nullary := true }

def kindToScala : CKind → Scala.Kind
  | .cls => .cls | .trt => .trt | .obj => .obj

def declToScala (c : Cls) (d : Decl) : Scala.Decl :=
  let parent : Cls × Ty → Scala.Parent := fun (p, a) => (clsName p, [tyToScala c a])
  { name := clsName c, kind := kindToScala d.kind, abs := d.abstract, final := d.final,
    tparams := if d.kind == .obj then 0 else 1
    super := d.parents.head?.map parent, traits := d.parents.tail.map parent
    members := d.decls.map fun (n, mm) => memToScala c n mm }

def classes : List Cls := [.A, .B, .M, .C, .X, .Y, .Z]

def program (src : Cls → Src) : Scala.Program :=
  classes.map fun c =>
    let d := declToScala c (src c).decl
    if (src c).decl.kind == .obj then { name := clsName c, obj := some d }
    else { name := clsName c, cls := some d }

/-- Run a shared-semantics computation over the program, reading objects as well as classes. -/
def runOn (src : Cls → Src) {α : Type} (m : Scala.M α) : Except String α :=
  let p := program src
  -- `need` asks for the class; an object of this space has no class, so serve the object instead
  let env : (q : Scala.Q) → Scala.Ans q := fun
    | .decl n _ => (p.find? (·.name = n)).bind fun s =>
        ((s.cls.or s.obj).map fun d => { decl := d })
  m.run.run env

/-- The shared linearization of `c`, without `c`, as `(class, type argument)`. -/
def sharedLin (src : Cls → Src) (c : Cls) : Except String (List (String × List Scala.Ty)) :=
  runOn src do
    let d ← Scala.need (clsName c)
    let l ← Scala.lin Scala.fuel d
    pure ((l.drop 1).map fun (a, ts) => (a.name, ts))

def toyLin (src : Cls → Src) (c : Cls) : List (String × List Scala.Ty) :=
  ((clean src c).iface.lin).map fun (p, a) => (clsName p, [tyToScala c a])

/-- The type a selection `c.n` has: the first member named `n` along `c`'s linearization, seen
from `c`. -/
def sharedSel (src : Cls → Src) (c : Cls) (n : Name) : Except String (Option Scala.Ty) :=
  runOn src do
    let d ← Scala.need (clsName c)
    let l ← Scala.lin Scala.fuel d
    pure (((Scala.hits l (nameStr n)).head?).map fun ((o, _), mem) =>
      Scala.seenFrom (clsName c) l o.name mem.res)

/-- The selections of `d`'s body, the toy's resolved types against the shared ones. -/
def selAgrees (src : Cls → Src) (d : Cls) : Bool :=
  ((src d).body.zip (clean src d).descs).all fun ((c, n), (_, t, _)) =>
    sharedSel src c n == .ok (t.map (tyToScala c))

/-- An error, by kind. -/
inductive EK | ovr | cfl | abs | other (s : String)
  deriving DecidableEq, Repr

def toyKinds (src : Cls → Src) (c : Cls) : List EK :=
  ((clean src c).errs.filterMap fun
    | .override _ => some EK.ovr | .conflict _ => some .cfl | .abstract _ => some .abs
    | .final _ => none).eraseDups

def sharedKinds (src : Cls → Src) (dl : Scala.Dialect := .s213) : Except String (List (String × EK)) := do
  let es ← Scala.Members.errors dl (program src)
  pure (es.map fun e => (e.cls, match e.kind with
    | .resultType | .stable | .lazyMismatch => EK.ovr
    | .conflicting | .accidental => .cfl
    | .needsAbstract => .abs
    | k => .other k.name)).eraseDups

def sameSet (a b : List EK) : Bool := a.all b.contains && b.all a.contains

def errsAgree (src : Cls → Src) (dl : Scala.Dialect := .s213) : Bool :=
  match sharedKinds src dl with
  | .ok es => classes.all fun c =>
      sameSet (toyKinds src c) ((es.filter (·.1 == clsName c)).map (·.2))
  | .error _ => false

def linAgrees (src : Cls → Src) : Bool :=
  classes.all fun c => sharedLin src c == .ok (toyLin src c)

/-- Per program: linearization, selections, refchecks. -/
def check (k : Cfg) (dl : Scala.Dialect := .s213) : Bool × Bool × Bool :=
  let src := k.src
  (linAgrees src, classes.all (selAgrees src), errsAgree src dl)

/-- Does each class compile? The toy's verdict (no error, a `final` parent included) against the
shared one. This is what an incremental build must reproduce; which errors are reported matters
less. -/
def verdictAgrees (src : Cls → Src) (dl : Scala.Dialect := .s213) : Bool :=
  match sharedKinds src dl with
  | .ok es => classes.all fun c =>
      ((clean src c).errs.filter (fun | .final _ => false | _ => true)).isEmpty ==
        (es.filter (·.1 == clsName c)).isEmpty
  | .error _ => false

/-- Where refchecks disagree: the classes and kinds each side reports, the toy's first. -/
def errPattern (k : Cfg) (dl : Scala.Dialect) : String :=
  let toy := classes.flatMap fun c => (toyKinds k.src c).map fun e => (clsName c, e)
  match sharedKinds k.src dl with
  | .ok sh => s!"{repr toy} vs {repr sh}"
  | .error e => s!"error {e}"

/-- Every 256th program of `FlatRules.cfgs`, so that the build checks the linearization and the
selections, which agree on the whole space; refchecks are `lake exe exhaustive flatshared`. -/
def sample : List Cfg := (cfgs.zipIdx.filter fun (_, i) => i % 256 == 0).map (·.1)

example : sample.all (fun k => linAgrees k.src && classes.all (selAgrees k.src)) = true := by
  native_decide

end Zinc.Flat.Shared
