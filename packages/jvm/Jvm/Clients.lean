import Jvm.Catalogue
/-!
# Client spaces: does an edit break *some* client?

MiMa reports a problem for an edit without naming a client; its claim is that some client compiled
against `v0` fails to link against `v1`. The model's version of that claim quantifies over a bounded
space of clients over the catalogue's universe:

- an optional client class `X`: superclass none, `A` or `B`; superinterfaces a subset of `I`, `J`;
  declares nothing, `m()V` or `m()I`;
- one call site: `invokestatic`, `invokevirtual`, `invokeinterface` of `m` with either descriptor on
  any owner, or `new` of any class; the receiver is a class whose static type is the owner in `v0`
  (`isSub`), as a compiler would emit it.

One site suffices: linking is lazy and per site, so a client fails on `v1` iff one of its sites
(or its loads) does. `breaksSomeClient` is the model's verdict for a MiMa problem; `changesSomeClient`
adds "links on both, and runs a different method" (the Track J4 verdict for `overrideAdded`, `pulledUp`).
Checked per catalogue case by kernel `decide`.

Not in the space: clients with more than one class, fields, `invokespecial`; and the verifier's
assignability checks, which a real client's `v1` receivers also face (`superclassRemoved` breaks
`B b; b.m()` compiled as `invokevirtual A.m` by a `VerifyError`).
-/

namespace Jvm.Clients

open Jvm.Catalogue

/-- `r` is `c` or a subtype of `c` in `w`, by superclasses and superinterfaces, with fuel. -/
def isSub (w : W) : Nat → C → C → Bool
  | 0, _, _ => false
  | k + 1, r, c =>
    r == c ||
      match w r with
      | none => false
      | some cf => (cf.header.super.toList ++ cf.header.ifaces).any fun s => isSub w k s c

def allC : List C := [.A, .B, .I, .J, .X]
def allD : List D := [.v, .i]

def xClasses : List (Classfile C N D) := do
  let s ← [none, some .A, some .B]
  let is ← [[], [.I], [.J], [.I, .J]]
  let ms ← [[], [(.m, .v, inst)], [(.m, .i, inst)]]
  pure { header := { super := s, ifaces := is }, methods := ms }

def sites : List (Site C N D) :=
  (allC.flatMap fun c => allD.map fun d => .invokestatic c .m d) ++
  (allC.flatMap fun c => allD.flatMap fun d => [.A, .B, .X].map fun r => .invokevirtual c .m d r) ++
  (allC.flatMap fun c => allD.flatMap fun d => [.A, .B, .X].map fun r => .invokeinterface c .m d r) ++
  allC.map .new

/-- A client: its classes and its program. -/
abbrev Client := List (C × Classfile C N D) × P

def space : List Client :=
  (sites.map fun s => ([], { sites := [s] })) ++
  (xClasses.flatMap fun x => sites.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

/-- The Track J3 space: `X` in the unnamed package, superclass none, `A` or `B`, implementing `I` or not,
declaring nothing or a public `m()V`; one site of any kind (methods `m()V`, fields `m:String`), run
from a class of its own or from `X` (`invokespecial` only from `X`). -/
def xClasses3 : List (Classfile C N D) := do
  let s ← [none, some .A, some .B]
  let is ← [[], [.I]]
  let ms ← [[], [(.m, .v, inst)]]
  pure { header := { super := s, ifaces := is }, methods := ms }

def sites3 : List (Site C N D) :=
  let rs : List C := [.A, .B, .X]
  let direct : List (Site C N D) :=
    (allC.flatMap fun c => rs.flatMap fun r =>
      [.invokevirtual c .m .v r, .invokeinterface c .m .v r, .getfield c .m .s r, .putfield c .m .s r]) ++
    (allC.flatMap fun c =>
      [.invokestatic c .m .v, .invokestaticIface c .m .v, .getstatic c .m .s, .putstatic c .m .s, .new c])
  direct ++ direct.map (.within .X) ++
    (allC.flatMap fun c => [true, false].map fun i => .within .X (.invokespecial c .m .v i))

def space3 : List Client :=
  (sites3.map fun s => ([], { sites := [s] })) ++
  (xClasses3.flatMap fun x => sites3.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

/-- The Track J5 space: `space3`'s clients, each `X` declaring a public `()V` constructor (Track J5's classes
declare theirs), plus `new c(…)` of each library class with `()V` and `(I)V`, from a class of its
own or from `X`. -/
def xClasses5 : List (Classfile C N D) := xClasses3.map fun x => { x with methods := ctor0 :: x.methods }

def sites5 : List (Site C N D) :=
  let cs : List (Site C N D) := [C.A, .B, .I, .J].flatMap fun c => [D.v, .iv].map fun d => .construct c .init d
  sites3 ++ cs ++ cs.map (.within .X)

def space5 : List Client :=
  (sites5.map fun s => ([], { sites := [s] })) ++
  (xClasses5.flatMap fun x => sites5.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

def recvOf : Site C N D → Option (C × C)
  | .invokevirtual c _ _ r => some (r, c)
  | .invokeinterface c _ _ r => some (r, c)
  | .getfield c _ _ r => some (r, c)
  | .putfield c _ _ r => some (r, c)
  | .within _ s => recvOf s
  | _ => none

/-- The client is one a compiler could emit against `w₀`: each receiver's class is a subtype of the
site's owner. -/
def wellTyped (w₀ : W) (p : P) : Bool :=
  p.sites.all fun s => match recvOf s with
    | some (r, c) => isSub w₀ depth r c
    | none => true

def _root_.Jvm.Catalogue.Case.withClient (k : Case) (cl : Client) : Case := { k with client := cl.1, prog := cl.2 }

def links (w : W) (p : P) : Bool := (outcome w p).toBool

/-- The first client in the space that links on `v0` and fails on `v1`. -/
def breaking (k : Case) (sp : List Client := space) : Option Client :=
  sp.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && !links k'.w1 p

def breaksSomeClient (k : Case) (sp : List Client := space) : Bool := (breaking k sp).isSome

/-- The first client that links on both and runs a different method. -/
def changing (k : Case) (sp : List Client := space) : Option Client :=
  sp.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && links k'.w1 p && k'.before != k'.after

def changesSomeClient (k : Case) (sp : List Client := space) : Bool := (changing k sp).isSome

/-! ## Verdicts per catalogue case -/

example : breaksSomeClient methodRemoved = true := by decide +kernel
example : breaksSomeClient resultTypeChanged = true := by decide +kernel
example : breaksSomeClient classBecomesInterface = true := by decide +kernel
example : breaksSomeClient becomesStatic = true := by decide +kernel
example : breaksSomeClient becomesAbstract = true := by decide +kernel
example : breaksSomeClient becomesFinal = true := by decide +kernel
example : breaksSomeClient methodBecomesFinal = true := by decide +kernel
example : breaksSomeClient superclassRemoved = true := by decide +kernel
example : breaksSomeClient defaultRemoved = true := by decide +kernel
example : breaksSomeClient defaultConflict = true := by decide +kernel
example : breaksSomeClient overrideAdded = false ∧ changesSomeClient overrideAdded = true := by
  decide +kernel
example : breaksSomeClient pulledUp = false ∧ changesSomeClient pulledUp = true := by decide +kernel

/-! ## Track J3 verdicts, over `space3` -/

example : breaksSomeClient methodBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient methodBecomesPackagePrivate space3 = true := by decide +kernel
example : breaksSomeClient classBecomesPackagePrivate space3 = true := by decide +kernel
example : breaksSomeClient methodBecomesProtected space3 = true := by decide +kernel
/-- Breaks `invokevirtual B.m`: resolution finds the private `B.m` before the inherited `A.m`. -/
example : breaksSomeClient overrideBecomesPrivate space3 = true ∧
    changesSomeClient overrideBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient superCallPulledUp space3 = false ∧
    changesSomeClient superCallPulledUp space3 = true := by decide +kernel
example : breaksSomeClient superCallRemoved space3 = true := by decide +kernel
example : breaksSomeClient superCallAbstract space3 = true := by decide +kernel
example : breaksSomeClient defaultSuperCallAbstract space3 = true := by decide +kernel
example : breaksSomeClient staticIfaceMethodRemoved space3 = true := by decide +kernel
example : breaksSomeClient staticMovedToIface space3 = true := by decide +kernel
example : breaksSomeClient defaultBecomesStatic space3 = true := by decide +kernel
example : breaksSomeClient defaultBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient fieldRemoved space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesStatic space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesFinal space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient fieldShadowed space3 = false ∧
    changesSomeClient fieldShadowed space3 = true := by decide +kernel
/-- Breaks `putstatic B.m`: it now resolves to the interface's field, which is final. -/
example : breaksSomeClient fieldIfaceBeforeSuper space3 = true ∧
    changesSomeClient fieldIfaceBeforeSuper space3 = true := by decide +kernel
example : breaksSomeClient putstaticBecomesFinal space3 = true := by decide +kernel


/-! ## Building calibration spaces

A calibration space is a product of named alternatives: library shapes, client shapes and sites. Each
alternative is a `Part`, a label and the classes and sites it contributes; `Part.and` multiplies two
lists of them, joining labels with commas, so a program's name lists every choice that made it. Each
program is a case with `v1 = v0`: it calibrates linking itself, not an edit. -/

/-- One choice in a space: its label, the library and client classes it adds, and its sites. -/
structure Part where
  label : String
  lib : List (C × Classfile C N D) := []
  client : List (C × Classfile C N D) := []
  sites : List (Site C N D) := []

/-- `p` then `q`: the label `p,q`, and both parts' classes and sites. -/
def Part.join (p q : Part) : Part :=
  { label := if p.label.isEmpty then q.label else if q.label.isEmpty then p.label else s!"{p.label},{q.label}",
    lib := p.lib ++ q.lib, client := p.client ++ q.client, sites := p.sites ++ q.sites }

/-- Every choice of `ps` with every choice of `qs`, in that order. -/
def Part.and (ps qs : List Part) : List Part := do
  let p ← ps
  let q ← qs
  pure (p.join q)

infixl:70 " ⊗ " => Part.and

def accs : List Access := [.pub, .prot, .pkg, .priv]

def accTag : Access → String | .pub => "pub" | .prot => "prot" | .pkg => "pkg" | .priv => "priv"

def cName : C → String | .A => "A" | .B => "B" | .I => "I" | .J => "J" | .X => "X"

/-- `m()V` with `mi`, or nothing. -/
def declM : Option MethodInfo → List (N × D × MethodInfo)
  | none => []
  | some mi => [(.m, .v, mi)]

/-- An optional choice's tag: `-` for none. -/
def optTag (f : α → String) : Option α → String
  | none => "-"
  | some a => f a

/-- The programs of a space named `space`: every choice of `parts` (a product of `Part` lists),
kept when it is well-typed against its library (each receiver a subtype of its owner). -/
def build (space : String) (parts : List Part) : List Case :=
  parts.filterMap fun p =>
    let k : Case := { name := s!"{space}/{p.label}", mima := none, v0 := p.lib, v1 := p.lib,
                      client := p.client, prog := { sites := p.sites } }
    if wellTyped k.w0 k.prog then some k else none

/-- The Track J6 space: overriding along a chain of library classes, the shape of JVMS §5.4.5's
example. `A` (package 1), `B extends A` and `I extends B` (`I` is a class here; `B` and `I` each in
package 1 or 2); `A` declares `m()V` with any access, final or not, and `B` and `I` each declare it
with any access or not at all. The client's `X extends I`, in the unnamed package, declares `m()V`
public, package-private, private or not at all; one `invokevirtual` of `A.m`, `B.m` or `I.m` on an
`X`, from a client class `J` in package 0, 1 or 2. Each program is a case with `v1 = v0`: it
calibrates selection (§5.4.6) and the load-time check for final methods (§5.3.5), both of which
use transitive overriding (§5.4.5 (b)). -/
def chainSpace : List Case :=
  let opt (a : Option Access) := declM (a.map fun a => { access := a })
  let tag := optTag accTag
  let a : List Part := do
    let acc ← accs
    let fin ← [false, true]
    pure { label := s!"A={accTag acc}{if fin then "+final" else ""}",
           lib := [(.A, { header := p1, methods := declM (some { access := acc, isFinal := fin }) })] }
  let below (c s : C) : List Part := do
    let acc ← none :: accs.map some
    let pkg ← [1, 2]
    pure { label := s!"{cName c}=p{pkg}.{tag acc}",
           lib := [(c, { header := { pkg, super := some s }, methods := opt acc })] }
  let x : List Part := [none, some .pub, some .pkg, some .priv].map fun acc =>
    { label := s!"X={tag acc}", client := [(.X, { header := { super := some .I }, methods := opt acc })] }
  let site : List Part := do
    let owner ← [C.A, .B, .I]
    let pkg ← [0, 1, 2]
    pure { label := s!"site={cName owner}.m@p{pkg}", client := [(.J, { header := { pkg } })],
           sites := [.within .J (.invokevirtual owner .m .v .X)] }
  build "chain" (a ⊗ below .B .A ⊗ below .I .B ⊗ x ⊗ site)

end Jvm.Clients
