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

Two finer queries, `Q.header` and `Q.member`, read the parts of a declaration the walk needs: the
granularity at which a bridge keys an inherited member. Linearization is written once over a
`Node` (`linWith`) and instantiated over whole declarations (`lin`) and over headers (`linH`);
`lookupH` is member lookup over headers and `member` queries. `ScalaTypes.Fine` proves the two
agree in every consistent environment.
-/

open Query

namespace Scala

/-- What linearization reads of a definition: its name, type parameters, kind and parents. -/
structure Header where
  name : String
  tparams : Nat := 0
  kind : Kind := .cls
  parents : List Parent := []
  deriving DecidableEq, Repr

def Decl.header (d : Decl) : Header := ⟨d.name, d.tparams, d.kind, d.parents⟩

/-- A definition's own member named `n`; a field without accessors is not one. -/
def Decl.member (d : Decl) (n : String) : Option Mem :=
  d.members.find? fun m => m.name == n && !m.fieldOnly

/-- The queries a unit asks of another definition. `decl` reads one side of its interface whole,
as lowering does. `header` and `member` read the class side's parts the walk needs, the
granularity a bridge keys on: they are projections of `decl` (`Consistent`). -/
inductive Q
  | decl (n : String) (isObj : Bool)
  | header (n : String)
  | member (n m : String)
  deriving DecidableEq, Repr

/-- A definition's interface, and whether this compiler run reads it from source (it is one of the
run's units) or from a pickle (TASTy, or Scala 2's pickle) on the classpath. -/
structure View where
  decl : Decl
  inRun : Bool := true
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .decl .. => Option View
  | .header _ => Option Header
  | .member .. => Option Mem

/-- The environment of a compiler run over the units `run` of `p`; the others are on the
classpath. -/
def Program.envIn (p : Program) (run : List String) : (q : Q) → Ans q
  | .decl n o => (p.find? (·.name = n)).bind fun s =>
    ((if o then s.obj else s.cls).map fun d => { decl := d, inRun := run.contains n })
  | .header n => (p.find? (·.name = n)).bind fun s => s.cls.map Decl.header
  | .member n m => (p.find? (·.name = n)).bind fun s => s.cls.bind (·.member m)

/-- The environment of one run over the whole program. -/
def Program.env (p : Program) : (q : Q) → Ans q := p.envIn (p.map (·.name))

abbrev M := ExceptT String (Query.Task Q Ans)

def askDecl (n : String) (o : Bool) : M (Option View) :=
  ExceptT.lift (Query.Task.ask (Q.decl n o) Query.Task.pure : Query.Task Q Ans (Option View))

def needView (n : String) : M View := do
  match ← askDecl n false with
  | some v => pure v
  | none => throw s!"not found: {n}"

def need (n : String) : M Decl := (·.decl) <$> needView n

def askHeader (n : String) : M (Option Header) :=
  ExceptT.lift (Query.Task.ask (Q.header n) Query.Task.pure : Query.Task Q Ans (Option Header))

def needHeader (n : String) : M Header := do
  match ← askHeader n with
  | some h => pure h
  | none => throw s!"not found: {n}"

def askMember (n m : String) : M (Option Mem) :=
  ExceptT.lift (Query.Task.ask (Q.member n m) Query.Task.pure : Query.Task Q Ans (Option Mem))

/-- An environment whose `header` and `member` answers are projections of its `decl` answers. -/
def Consistent (e : (q : Q) → Ans q) : Prop :=
  (∀ n, e (.header n) = (e (.decl n false) : Option View).map (·.decl.header)) ∧
  ∀ n m, e (.member n m) = (e (.decl n false) : Option View).bind (·.decl.member m)

theorem Program.envIn_consistent (p : Program) (run : List String) : Consistent (p.envIn run) := by
  refine ⟨fun n => ?_, fun n m => ?_⟩ <;>
  · simp only [Program.envIn, Bool.false_eq_true, ↓reduceIte]
    cases p.find? (·.name = n) with
    | none => rfl
    | some s => simp only [Option.bind_some]; cases s.cls <;> rfl

/-! ## Linearization and member lookup -/

/-- A base class with its type argument as the class being lowered sees it: `C.this baseType A`.
The class itself comes first, applied to its own parameter. -/
abbrev Anc := Decl × List Ty

/-- The base-type facts of a top-level class `self` whose base classes, by name, are `l`, for
`AsSeenFrom`. Only `self.this` has base types; the prefix of a top-level class is its package,
where the walk stops. -/
def namedWorld (self : String) (l : List (String × List Ty)) : AsSeenFrom.World String Ty where
  bpre _ _ := .this []
  hasBase p c := p == .this [self] && l.any fun (a, _) => [a] == c
  bargs p c := if p == .this [self] then
      ((l.find? fun (a, _) => [a] == c).map (·.2)).getD []
    else []

/-- The base-type facts of `self` with base classes `l`. -/
def classWorld (self : String) (l : List Anc) : AsSeenFrom.World String Ty :=
  namedWorld self (l.map fun (a, ts) => (a.name, ts))

/-- `info.asSeenFrom(self.this, owner)`, for base classes by name. -/
def seenFromN (self : String) (l : List (String × List Ty)) (owner : String) (t : Ty) : Ty :=
  AsSeenFrom.asf (namedWorld self l) (.this [self]) [owner] t

/-- `info.asSeenFrom(self.this, owner)`. -/
def seenFrom (self : String) (l : List Anc) (owner : String) (t : Ty) : Ty :=
  seenFromN self (l.map fun (a, ts) => (a.name, ts)) owner t

/-- What the linearization walk reads of a definition, and how it fetches a parent by name. The
walk is written once, over a `Node`: `Node.decl` reads whole declarations (`Q.decl`), as lowering
and refchecks do; `Node.header` reads only headers (`Q.header`), the granularity a bridge keys on. -/
structure Node (N : Type) where
  name : N → String
  tparams : N → Nat
  parents : N → List Parent
  fetch : String → M N

def Node.decl : Node Decl := ⟨Decl.name, Decl.tparams, Decl.parents, need⟩

/-- A header node keeps the name it was fetched by, which is what its `member` queries ask. -/
def Node.header : Node (String × Header) :=
  ⟨(·.2.name), (·.2.tparams), (·.2.parents), fun n => do pure (n, ← needHeader n)⟩

section Walk
variable {N : Type} (nd : Node N)

/-- Merge the parents' linearizations onto `acc`, left to right: a later parent's classes go
first, a class already in `acc` is not repeated. A parent `P[a]`'s base types are viewed from
`self` by `asSeenFrom(self.this, P)`, which replaces `P`'s parameter by `a` (scalac's
`baseType`). -/
def linMerge (self : String) (rec : N → M (List (N × List Ty))) :
    List (N × List Ty) → List Parent → M (List (N × List Ty))
  | acc, [] => pure acc
  | acc, (p, pa) :: rest => do
    let pd ← nd.fetch p
    let lp ← rec pd
    let w := namedWorld self [(nd.name pd, pa)]
    let lp := lp.map fun (a, ts) => (a, ts.map (AsSeenFrom.asf w (.this [self]) [p]))
    linMerge self rec (lp.filter (fun e => !acc.any (nd.name ·.1 == nd.name e.1)) ++ acc) rest

/-- Scala's linearization, the class first: `L(C) = C, L(Pn) +⃗ … +⃗ L(P1)`, each class with its
type arguments as `C` sees them. -/
def linWith : Nat → N → M (List (N × List Ty))
  | 0, _ => throw "linearization too deep"
  | k + 1, d => do
    let acc ← linMerge nd (nd.name d) (linWith k) [] (nd.parents d)
    pure ((d, (List.range (nd.tparams d)).map (Ty.tp [nd.name d])) :: acc)

end Walk

/-- Scala's linearization over whole declarations. -/
def lin : Nat → Decl → M (List Anc) := linWith Node.decl

/-- Scala's linearization over headers: the same walk, asking only `header`. -/
def linH : Nat → String × Header → M (List ((String × Header) × List Ty)) := linWith Node.header

def fuel : Nat := 8

/-- A member as seen from the class: its owner, the owner's type argument, the member. -/
abbrev Hit := Anc × Mem

/-- The members named `n` along the linearization `l` of a class (the class first). A private
member is not inherited: only the class's own private members are seen. -/
def hits (l : List Anc) (n : String) : List Hit :=
  let self := (l.head?.map (·.1.name)).getD ""
  l.filterMap fun (d, a) => ((d.members.find? fun m => m.name == n && !m.fieldOnly).filter fun m => !m.priv || d.name == self).map
    fun m => ((d, a), m)

/-- The first member named `n` along `l` that class `self` sees, reading each class's own member
with `mem` and stopping at the first: `hits`'s head (`Scala.firstHit_decl`), without reading the
classes after it. -/
def firstHitWith {N : Type} (nd : Node N) (mem : N → String → M (Option Mem)) (self n : String) :
    List (N × List Ty) → M (Option ((N × List Ty) × Mem))
  | [] => pure none
  | (d, a) :: rest => do
    match (← mem d n).filter fun m => !m.priv || nd.name d == self with
    | some m => pure (some ((d, a), m))
    | none => firstHitWith nd mem self n rest

/-- `firstHitWith` from the class at the head of `l`. -/
def firstHitIn {N : Type} (nd : Node N) (mem : N → String → M (Option Mem)) (n : String)
    (l : List (N × List Ty)) : M (Option ((N × List Ty) × Mem)) :=
  firstHitWith nd mem ((l.head?.map (nd.name ·.1)).getD "") n l

/-- Over headers, each class asked for its own member named `n` (`Q.member`). -/
def firstHitH (n : String) (l : List ((String × Header) × List Ty)) :
    M (Option (((String × Header) × List Ty) × Mem)) :=
  firstHitIn Node.header (fun h n => askMember h.1 n) n l

/-- Member lookup over headers: the type of `c.n` as `c` sees it, the first member named `n`
along `c`'s linearization viewed from `c`. Asks only `header` and `member`. -/
def lookupH (fuel : Nat) (c n : String) : M (Option Ty) := do
  let l ← linH fuel (← Node.header.fetch c)
  let some (((_, o), _), m) ← firstHitH n l | pure none
  pure (some (seenFromN c (l.map fun (h, ts) => (h.2.name, ts)) o.name m.res))

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
