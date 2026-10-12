import Query.Basic
import Query.Task
import ScalaTypes.Syntax
/-!
# Resolution over interfaces, as a `Task`

A unit's view of other definitions is a query, `Q.decl`, which is what scalac reads from pickles
or TASTy. On top of it: linearization (`lin`), a member's type as seen from a class
(`seenFrom`, through `AsSeenFrom`), the members a name selects along the linearization (`hits`),
signature groups, and the member a selection runs (`winner`). `Members` checks overriding with
these; `Scala.Lower` (in the `Scala` package) adds erasure and code generation.
-/

namespace Scala

inductive Q | decl (n : String) (isObj : Bool)
  deriving DecidableEq, Repr

/-- A definition's interface, and whether this compiler run reads it from source (it is one of the
run's units) or from a pickle (TASTy, or Scala 2's pickle) on the classpath. -/
structure View where
  decl : Decl
  inRun : Bool := true
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .decl .. => Option View

/-- The environment of a compiler run over the units `run` of `p`; the others are on the
classpath. -/
def Program.envIn (p : Program) (run : List String) : (q : Q) → Ans q
  | .decl n o => (p.find? (·.name = n)).bind fun s =>
    ((if o then s.obj else s.cls).map fun d => { decl := d, inRun := run.contains n })

/-- The environment of one run over the whole program. -/
def Program.env (p : Program) : (q : Q) → Ans q := p.envIn (p.map (·.name))

abbrev M := ExceptT String (Zinc.Task Q Ans)

def askDecl (n : String) (o : Bool) : M (Option View) :=
  ExceptT.lift (Zinc.Task.ask (Q.decl n o) Zinc.Task.pure : Zinc.Task Q Ans (Option View))

def needView (n : String) : M View := do
  match ← askDecl n false with
  | some v => pure v
  | none => throw s!"not found: {n}"

def need (n : String) : M Decl := (·.decl) <$> needView n

/-! ## Linearization and member lookup -/

/-- A base class with its type argument as the class being lowered sees it: `C.this baseType A`.
The class itself comes first, applied to its own parameter. -/
abbrev Anc := Decl × List Ty

/-- The base-type facts of a top-level class `self` with base classes `l`, for `AsSeenFrom`. Only
`self.this` has base types; the prefix of a top-level class is its package, where the walk stops. -/
def classWorld (self : String) (l : List Anc) : AsSeenFrom.World String Ty where
  bpre _ _ := .this []
  hasBase p c := p == .this [self] && l.any fun (a, _) => [a.name] == c
  bargs p c := if p == .this [self] then
      ((l.find? fun (a, _) => [a.name] == c).map (·.2)).getD []
    else []

/-- `info.asSeenFrom(self.this, owner)`. -/
def seenFrom (self : String) (l : List Anc) (owner : String) (t : Ty) : Ty :=
  AsSeenFrom.asf (classWorld self l) (.this [self]) [owner] t

/-- Scala's linearization, the class first: `L(C) = C, L(Pn) +⃗ … +⃗ L(P1)`. A parent `P[a]`'s base
types are viewed from `C` by `asSeenFrom(C.this, P)`, which replaces `P`'s parameter by `a`
(scalac's `baseType`). -/
def lin : Nat → Decl → M (List Anc)
  | 0, _ => throw "linearization too deep"
  | k + 1, d => do
    let mut acc : List Anc := []
    for (p, pa) in d.parents do
      let pd ← need p
      let lp ← lin k pd
      let w := classWorld d.name [(pd, pa)]
      let lp := lp.map fun (a, ts) => (a, ts.map (AsSeenFrom.asf w (.this [d.name]) [p]))
      acc := lp.filter (fun e => !acc.any (·.1.name == e.1.name)) ++ acc
    pure ((d, (List.range d.tparams).map (Ty.tp [d.name])) :: acc)

def fuel : Nat := 8

/-- A member as seen from the class: its owner, the owner's type argument, the member. -/
abbrev Hit := Anc × Mem

/-- The members named `n` along the linearization `l` of a class (the class first). A private
member is not inherited: only the class's own private members are seen. -/
def hits (l : List Anc) (n : String) : List Hit :=
  let self := (l.head?.map (·.1.name)).getD ""
  l.filterMap fun (d, a) => ((d.members.find? fun m => m.name == n && !m.fieldOnly).filter fun m => !m.priv || d.name == self).map
    fun m => ((d, a), m)

/-- The inherited members named `n`. -/
def hitsAbove (l : List Anc) (n : String) : List Hit :=
  let self := (l.head?.map (·.1.name)).getD ""
  (hits l n).filter (·.1.1.name != self)

/-- `C.this.memberType(m)`'s parameter types, for a member `m` of base class `owner` of `C`. -/
def paramsSeen (self : String) (l : List Anc) (h : Hit) : List Ty :=
  h.2.allParams.map (seenFrom self l h.1.1.name)

/-- Does `h` override (or implement) `h'` in `C`? Same name, and the same parameter types as seen
from `C` (`matches` after `memberType`); otherwise they are overloads. -/
def overridesIn (self : String) (l : List Anc) (h h' : Hit) : Bool :=
  h.2.name == h'.2.name && paramsSeen self l h == paramsSeen self l h'

def memberNames (l : List Anc) : List String :=
  Query.dedupLast (l.flatMap fun (d, _) => d.members.map (·.name))

def Hit.same (h h' : Hit) : Bool := h.1.1.name == h'.1.1.name && h.2 == h'.2

/-- The members of `C` by signature: each name's hits, grouped by `overridesIn` (members that
override one another as seen from `C`), in linearization order. Overloads are separate groups. -/
def sigGroups (self : String) (l : List Anc) : List (List Hit) :=
  (memberNames l).flatMap fun n =>
    (hits l n).foldl (init := []) fun gs h =>
      match gs.findIdx? fun g => (g.head?.map fun r => overridesIn self l r h).getD false with
      | some i => gs.modify i (· ++ [h])
      | none => gs ++ [[h]]

/-- The member a group resolves to: the first concrete one, else the first. -/
def winner (g : List Hit) : Option Hit := (g.find? (!·.2.abs)).or g.head?

/-- Member lookup by signature: what `h`'s group resolves to in `C`. -/
def lookupSig (self : String) (l : List Anc) (h : Hit) : Option Hit :=
  ((sigGroups self l).find? fun g => g.any (Hit.same h)).bind winner

/-- Is a member in the classfile? A Scala 3 `inline def` is not, unless it overrides or implements
an inherited member (then it is *retained*). -/
def retained (self : String) (l : List Anc) (h : Hit) : Bool :=
  !h.2.inline || (hitsAbove l h.2.name).any (overridesIn self l h)

/-- Traits mixed in by `d` itself: those before the superclass's linearization. -/
def mixins (d : Decl) (l : List Anc) : M (List Anc) := do
  match d.super with
  | none => pure (l.tail.filter (·.1.kind == .trt))
  | some (s, _) =>
    let ls ← lin fuel (← need s)
    pure (l.tail.filter fun e => e.1.kind == .trt && !ls.any (·.1.name == e.1.name))

end Scala
