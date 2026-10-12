import Zinc.Bridges.HierSound
/-!
# `Hier`'s lookup is the shared semantics

`Hier`'s programs are written in a small syntax (eight class names, two member names, a four-case
`Ty`) and lowered to the shared one (`Decl.toScala`); its member lookup is the shared walk over
headers (`Scala.lookupH`), its queries mapped to `Hier`'s by `toQ`. This file proves that what a
client of `Hier` resolves is what the shared semantics resolves over whole declarations:

* `program`: a `Hier` program as a `Scala.Program`;
* `shared`: member lookup there, scalac's way (`Scala.lookup`): the linearization (`Scala.lin`), the
  first member named `n` along it (`Scala.hits`), viewed from the class (`Scala.seenFrom`);
* `toy_eq_shared`: for **every** `Hier` program, class and member name, `Hier.resolve` gives what
  `shared` gives (a failed lookup selecting nothing). From `Scala.lookupH_eq`, and from `toQ`
  answering the walk's queries as the program's environment does (`through_agrees`).

History: before Phase 29 (`packages/zinc/docs/29-shared-scala.md`), `Hier` had its own walk and
`asSeenFrom`, and this file checked agreement on a space of 1,638,400 hierarchies over `A`, `B`,
`M`, `C` (`lake exe exhaustive hiershared`, every 64th in the build). That check found that
`Hier`'s first walk (depth first, the last parent first) agreed only on tree-shaped hierarchies up
to depth 2 (290,560 of them): in `class C extends M with A`, with `M extends A`, it reached `A`
directly, where Scala's linearization is `C, M, A` and `M.m` overrides `A.m`. `Hier` then followed
the linearization, and now uses the shared walk itself, so the check is this theorem.
-/

open Query

namespace Zinc.Hier.Shared

open Hier

def program (decls : Cls → Hier.Decl) : Scala.Program :=
  Cls.all.map fun c => { name := c.name, cls := some (Decl.toScala c (decls c)) }

/-- The toy: `Hier.resolve` from `c`, as a client of `c` asks it. -/
def toy (decls : Cls → Hier.Decl) (c : Cls) (n : Name) : Option Scala.Ty :=
  (resolve c n).run (envOfI fun d => ⟨Decl.toScala d (decls d), []⟩)

/-- The shared semantics over whole declarations. -/
def shared (decls : Cls → Hier.Decl) (c : Cls) (n : Name) : Except String (Option Scala.Ty) :=
  Scala.ex (Scala.Program.env (program decls)) (Scala.lookup fuel c.name n.str)

theorem find?_program (decls : Cls → Hier.Decl) (s : String) :
    (program decls).find? (·.name = s) =
      (Cls.ofName? s).map fun c => { name := c.name, cls := some (Decl.toScala c (decls c)) } := by
  simp only [program, Cls.ofName?, List.find?_map]
  rfl

/-- `toQ` answers the walk's queries as the program's environment does. -/
theorem through_agrees (decls : Cls → Hier.Decl) :
    ∀ q, Scala.Walky q →
      Query.Task.Env.through toQ (envOfI fun d => ⟨Decl.toScala d (decls d), []⟩) q =
        Scala.Program.env (program decls) q
  | .decl .., h => h.elim
  | .header s, _ => by
    simp only [Query.Task.Env.through, toQ, Scala.Program.env, Scala.Program.envIn, find?_program]
    cases Cls.ofName? s <;> rfl
  | .member s m, _ => by
    simp only [Query.Task.Env.through, toQ, Scala.Program.env, Scala.Program.envIn, find?_program]
    cases Cls.ofName? s <;> rfl

/-- **`Hier`'s lookup is the shared semantics**, for every program, class and name. -/
theorem toy_eq_shared (decls : Cls → Hier.Decl) (c : Cls) (n : Name) :
    toy decls c n = ofExcept (shared decls c n) := by
  let e := envOfI fun d => ⟨Decl.toScala d (decls d), []⟩
  let x := Scala.lookupH fuel c.name n.str
  have hrun : (resolve c n).run e = ofExcept (Scala.ex (Query.Task.Env.through toQ e) x) := by
    simp only [resolve, Task.bind_eq, Task.run_bind, Task.pure_eq, Task.run_pure,
      Query.Task.run_interp]
    rfl
  have hcongr : Scala.ex (Query.Task.Env.through toQ e) x =
      Scala.ex (Scala.Program.env (program decls)) x :=
    Task.run_congr _ _ _ fun q hq =>
      through_agrees decls q (Scala.asks_lookupH _ fuel c.name n.str q hq)
  show (resolve c n).run e = _
  rw [hrun, hcongr]
  exact congrArg ofExcept
    (Scala.lookupH_eq (program decls).env (Scala.Program.envIn_consistent _ _) _ _ _)

/-! ## The scenarios of `Hier`, by evaluation -/

def agrees (decls : Cls → Hier.Decl) : Bool :=
  [Cls.A, .B, .M, .C].all fun c => [Name.m, .g].all fun n =>
    shared decls c n == .ok (toy decls c n)

example : agrees fun c => (base c).decl := by decide
example : agrees fun c => (edit1 c).decl := by decide
example : agrees fun c => (edit2 c).decl := by decide
example : agrees fun c => (edit3 c).decl := by decide

/-! ## A bounded space of hierarchies

Every hierarchy over `A`, `B`, `M`, `C`: each class's parents drawn from the classes before it, at
most two, each parent's type argument and each declaration of `m` one of `Int`, `String` or the
class's parameter; 1,638,400 hierarchies. Agreement with the shared semantics no longer needs
checking on it (`toy_eq_shared`); it is the space on which the shared semantics is to be
calibrated against scalac and dotc (`packages/harness/docs/compile-server.md`). -/

def tys : List Hier.Ty := [.int, .string, .param]

/-- Ordered lists of distinct parents from `ps`, at most two. -/
def parentLists (ps : List Cls) : List (List Cls) :=
  [] :: ps.map ([·]) ++ ps.flatMap fun p => (ps.filter (· ≠ p)).map fun q => [p, q]

def withArgs : List Cls → List (List (Cls × Hier.Ty))
  | [] => [[]]
  | p :: ps => tys.flatMap fun a => (withArgs ps).map ((p, a) :: ·)

def declsOf : List (List (Name × Hier.Ty)) := [] :: tys.map fun t => [(.m, t)]

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

/-- `asSeenFrom` on `Hier`'s toy types: instantiate the parameter. -/
def substTy (arg : Hier.Ty) : Hier.Ty → Hier.Ty
  | .param => arg
  | t => t

/-- Every base class of `c` along every path, with its type argument as seen from `c`. -/
def bases (decls : Cls → Hier.Decl) : Nat → Cls → Hier.Ty → List (Cls × Hier.Ty)
  | 0, _, _ => []
  | k + 1, c, arg => (decls c).parents.flatMap fun (p, a) =>
    (p, substTy arg a) :: bases decls k p (substTy arg a)

/-- No class has a base class with two different type arguments (scalac rejects that). -/
def consistent (decls : Cls → Hier.Decl) : Bool :=
  [Cls.A, .B, .M, .C].all fun c =>
    let bs := bases decls 4 c .param
    bs.all fun (p, a) => bs.all fun (q, b) => p != q || a == b

end Zinc.Hier.Shared
