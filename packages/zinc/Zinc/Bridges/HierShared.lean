import Zinc.Bridges.Hier
import ScalaTypes.Resolve
/-!
# `Hier`'s toy Scala, embedded in the shared Scala semantics

`Hier` has its own small Scala: eight class names, two member names, a four-case `Ty`, one type
parameter per class, and member lookup as a walk over the parents, the last parent first. That
language is kept small on purpose, so that its programs can be enumerated. This file says what it
means in the shared semantics (`ScalaTypes`):

* `Ty.toScala`, `Decl.toScala`, `program`: a `Hier` program as a `Scala.Program`. The class's
  parameter becomes `Scala.Ty.tp [C] 0`, a parent's type argument is written in the child's scope;
* `shared`: member lookup there, scalac's way: the linearization (`Scala.lin`), the first member
  named `n` along it (`Scala.hits`), viewed from the class (`Scala.seenFrom`);
* `agrees`: `Hier.resolve` and `shared` give the same type for every class and member.

The five scenarios of `Hier` agree (kernel `decide`, below).

`space` enumerates hierarchies over `A`, `B`, `M`, `C`: each class's parents drawn from the classes
before it, at most two, each parent's type argument and each declaration of `m` one of `Int`,
`String` or the class's parameter; 1,638,400 hierarchies. `lake exe exhaustive hiershared`
compares the two semantics on every one, and they agree on all of them: tree-shaped or not, up to
depth 3, and also where scalac would reject the program for inconsistent type arguments (both
keep the first, as `lin` does).

History: `Hier` first walked the parents depth first, the last parent first, and agreed only on
tree-shaped hierarchies up to depth 2 (290,560 of them). With a shared ancestor it differed: in
`class C extends M with A`, with `M extends A`, it reached `A` directly, where Scala's
linearization is `C, M, A` and `M.m` overrides `A.m`. `Hier.resolve` now follows the
linearization; the scenarios and the designs' obligations (`HierSound`) are unchanged.
-/

open Query

namespace Zinc.Hier.Shared

open Hier

def clsName : Cls → String
  | .A => "A" | .B => "B" | .M => "M" | .C => "C" | .X => "X" | .Y => "Y" | .Z => "Z" | .V => "V"

def nameStr : Name → String
  | .m => "m" | .g => "g"

/-- A type of `Hier`, written in class `self`. -/
def Ty.toScala (self : Cls) : Hier.Ty → Scala.Ty
  | .int => .int
  | .string => .str
  | .param => .tp [clsName self] 0
  | .v => .ref "V"

def Decl.toScala (c : Cls) (d : Hier.Decl) : Scala.Decl :=
  let parent : Cls × Hier.Ty → Scala.Parent := fun (p, a) => (clsName p, [Ty.toScala c a])
  { name := clsName c
    tparams := 1
    super := d.parents.head?.map parent
    traits := d.parents.tail.map parent
    members := d.decls.map fun (n, t) => { name := nameStr n, res := Ty.toScala c t } }

def program (decls : Cls → Hier.Decl) : Scala.Program :=
  [Cls.A, .B, .M, .C, .X, .Y, .Z, .V].map fun c =>
    { name := clsName c, cls := some (Decl.toScala c (decls c)) }

/-- The toy: `Hier.resolve` from `c`, as a client of `c` asks it (the result in `c`'s scope). -/
def toy (decls : Cls → Hier.Decl) (c : Cls) (n : Name) : Option Hier.Ty :=
  (resolve 3 c n .param).run (envOfI fun d => ⟨decls d, []⟩)

/-- The shared semantics: the first member named `n` along `c`'s linearization, seen from `c`. -/
def shared (decls : Cls → Hier.Decl) (c : Cls) (n : Name) : Except String (Option Scala.Ty) :=
  let m : Scala.M (Option Scala.Ty) := do
    let d ← Scala.need (clsName c)
    let l ← Scala.lin Scala.fuel d
    pure (((Scala.hits l (nameStr n)).head?).map fun ((o, _), mem) =>
      Scala.seenFrom (clsName c) l o.name mem.res)
  m.run.run (Scala.Program.env (program decls))

/-- The toy and the shared semantics agree on member `n` of `c`. -/
def agreesOn (decls : Cls → Hier.Decl) (c : Cls) (n : Name) : Bool :=
  shared decls c n == .ok ((toy decls c n).map (Ty.toScala c))

def agrees (decls : Cls → Hier.Decl) : Bool :=
  [Cls.A, .B, .M, .C].all fun c => [Name.m, .g].all fun n => agreesOn decls c n

/-! ## The scenarios of `Hier` -/

example : agrees fun c => (base c).decl := by decide
example : agrees fun c => (edit1 c).decl := by decide
example : agrees fun c => (base2 c).decl := by decide
example : agrees fun c => (edit2 c).decl := by decide
example : agrees fun c => (edit3 c).decl := by decide

/-! ## A bounded space of hierarchies -/

def tys : List Hier.Ty := [.int, .string, .param]

/-- Ordered lists of distinct parents from `ps`, at most two. -/
def parentLists (ps : List Cls) : List (List Cls) :=
  [] :: ps.map ([·]) ++ ps.flatMap fun p => (ps.filter (· ≠ p)).map fun q => [p, q]

def withArgs : List Cls → List (List (Cls × Hier.Ty))
  | [] => [[]]
  | p :: ps => tys.flatMap fun a => (withArgs ps).map ((p, a) :: ·)

def declsOf : List (List (Name × Hier.Ty)) := [] :: tys.map fun t => [(.m, t)]

/-- Every hierarchy over `A`, `B`, `M`, `C` (each class's parents among the classes before it). -/
def space : List (Cls → Hier.Decl) :=
  (parentLists [.A]).flatMap fun pB => (withArgs pB).flatMap fun aB =>
  (parentLists [.A, .B]).flatMap fun pM => (withArgs pM).flatMap fun aM =>
  (parentLists [.A, .B, .M]).flatMap fun pC => (withArgs pC).flatMap fun aC =>
  declsOf.flatMap fun dA => declsOf.flatMap fun dB => declsOf.flatMap fun dM =>
  declsOf.map fun dC => fun
    | .A => { decls := dA }
    | .B => { parents := aB, decls := dB }
    | .M => { parents := aM, decls := dM }
    | .C => { parents := aC, decls := dC }
    | _ => {}

/-- No class reaches an ancestor along two paths. -/
def treeShaped (decls : Cls → Hier.Decl) : Bool :=
  let parents (c : Cls) := (decls c).parents.map (·.1)
  let rec anc : Nat → Cls → List Cls
    | 0, _ => []
    | k + 1, c => (parents c).flatMap fun p => p :: anc k p
  [Cls.A, .B, .M, .C].all fun c => let a := anc 4 c; a.length == (Query.dedupLast a).length

/-- The longest chain of parents from any class. -/
def depth (decls : Cls → Hier.Decl) : Nat :=
  let rec go : Nat → Cls → Nat
    | 0, _ => 0
    | k + 1, c => ((decls c).parents.map fun (p, _) => go k p + 1).foldl max 0
  [Cls.A, .B, .M, .C].foldl (fun m c => max m (go 4 c)) 0

/-- Every base class of `c` along every path, with its type argument as seen from `c`. -/
def bases (decls : Cls → Hier.Decl) : Nat → Cls → Hier.Ty → List (Cls × Hier.Ty)
  | 0, _, _ => []
  | k + 1, c, arg => (decls c).parents.flatMap fun (p, a) =>
    (p, Hier.Ty.subst arg a) :: bases decls k p (Hier.Ty.subst arg a)

/-- No class has a base class with two different type arguments (scalac rejects that). -/
def consistent (decls : Cls → Hier.Decl) : Bool :=
  [Cls.A, .B, .M, .C].all fun c =>
    let bs := bases decls 4 c .param
    bs.all fun (p, a) => bs.all fun (q, b) => p != q || a == b

/-- Every 64th hierarchy of `space`, so that the build checks agreement (about 25,600; the whole
space is `lake exe exhaustive hiershared`). A change to `Hier` or to the shared semantics that
breaks agreement fails here. -/
def sample : List (Cls → Hier.Decl) :=
  (space.zipIdx.filter fun (_, i) => i % 64 == 0).map (·.1)

example : sample.all agrees = true := by native_decide

end Zinc.Hier.Shared
