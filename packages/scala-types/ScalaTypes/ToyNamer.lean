import Query.Lazy
import Query.Interrupt
/-!
# The toy language's namer as rules

Track I's toy language (`packages/scala/probes/interrupt`: classes, objects and traits with members
whose types are declared or inferred from a path, no expressions) gets its lazy facts here as a
function of the program: `rulesOf cut p` is the namer. It decides which facts exist (a class's
member names, its parent, each member's type) and what each completer asks, bundled as one of three
compilers would bundle it (`Cut`). This is where Track L's theorems, which so far quantified over
hand-written rule sets (`ScalaTypes.Laziness`), meet a language: `Query.Lazy.force` on `rulesOf`
is the symbol table of any toy program, `forcePeek` and `Query.Interrupt.forceT` its peeking and
tainted variants, and the Java kernels' forcing traces are what these rules must reproduce.

The language has one feature the Java toy does not yet: Scala 3's `export`, the shape of Track L's
findings L2 and L9, because it is where the cuts differ. A member set that includes forwarders is a
fact that reads another class's member set; dotc reads it as indexed so far when it is in progress
(`TempClassInfo`), and a forwarder needs the member's type, which it skips when that is in progress.
Both are peeks (`Query.Lazy.Probe.peek`), and both findings fall out of `forcePeek` on these rules
by `decide`; under full taint (`forceT`) L9 is order-independent, and under the fine cut L2 is a
true cycle of the names themselves.
-/

namespace ScalaTypes.ToyNamer

open Query Query.Lazy

/-! ## The language -/

/-- `def name: declared` or `def name = path`. -/
structure Member where
  name : String
  declared : Option String := none
  path : List String := []
  deprecated : Bool := false
  deriving DecidableEq, Repr

inductive Stat
  | member (m : Member)
  /-- `export src.*` (`names = none`) or `export src.{names}`; Scala 3 only. -/
  | export (src : String) (names : Option (List String))
  deriving DecidableEq, Repr

structure Decl where
  obj : Bool := false
  isCase : Bool := false
  isImplicit : Bool := false
  nowarn : Bool := false
  name : String
  params : List (String × String) := []
  parent : Option String := none
  stats : List Stat := []
  deriving DecidableEq, Repr

abbrev Program := List Decl

/-- A class or an object by name: the two namespaces of the toy. -/
structure Ref where
  name : String
  obj : Bool
  deriving DecidableEq, Repr

def cls (n : String) : Ref := ⟨n, false⟩
def obj (n : String) : Ref := ⟨n, true⟩

/-- The declaration of `r`, or a case class's synthetic companion. -/
def findDecl (p : Program) (r : Ref) : Option Decl :=
  match p.find? fun d => d.name == r.name && d.obj == r.obj with
  | some d => some d
  | none =>
    if r.obj && (p.any fun d => d.name == r.name && !d.obj && d.isCase) then
      some { obj := true, name := r.name }
    else none

def isCaseClass (p : Program) (n : String) : Bool := p.any fun d => d.name == n && !d.obj && d.isCase

def Decl.members (d : Decl) : List Member :=
  d.stats.filterMap fun | .member m => some m | _ => none

def Decl.exports (d : Decl) : List (String × Option (List String)) :=
  d.stats.filterMap fun | .export f ns => some (f, ns) | _ => none

/-- The synthetic members: a case class's `copy`, `equals`, `hashCode`, `toString`; its companion's
`apply` and `unapply`. -/
def synthetics (p : Program) (r : Ref) : List String :=
  if !r.obj && isCaseClass p r.name then ["copy", "equals", "hashCode", "toString"]
  else if r.obj && isCaseClass p r.name then ["apply", "unapply"]
  else []

/-- The names `r` declares in the source, with its synthetics: the level-1 fact the namer has
without asking anything (dotc's `TempClassInfo`, scalac's scope after `enterSym`). -/
def ownNames (p : Program) (r : Ref) : List String :=
  match findDecl p r with
  | none => []
  | some d =>
    (if d.isCase && !d.obj then d.params.map (·.1) else []) ++ d.members.map (·.name) ++ synthetics p r

/-! ## The facts -/

inductive Fact
  /-- Level 1: `r`'s member names, forwarders included. -/
  | decls (r : Ref)
  /-- Level 1: `r`'s parent. -/
  | info (r : Ref)
  /-- Level 2: the type of member `name` of `owner`. -/
  | mem (owner : Ref) (name : String)
  deriving DecidableEq, Repr

inductive Ty
  | ref (r : Ref)
  | builtin (n : String)
  | err (msg : String)
  deriving DecidableEq, Repr

/-- A step of a path that went through an implicit class: the class, the member it supplied and the
type it was applied to. -/
structure Via where
  cls : String
  member : String
  onType : String
  deriving DecidableEq, Repr

/-- A member's type, with how it was reached: the implicit view a step of the path went through, and
the deprecated members (owner, name) the path referred to. The kernel reads both. -/
structure Typed where
  ty : Ty
  via : Option Via := none
  deprecated : List (Ref × String) := []
  deriving DecidableEq, Repr

inductive Value
  | names (ns : List String)
  | parent (p : Option String)
  | typed (t : Typed)
  | err (msg : String)
  deriving DecidableEq, Repr

def ty (t : Ty) : Value := .typed { ty := t }

/-- The answer a peek gets for a fact in progress. -/
def absent : Value := .err "absent"

/-- How a compiler bundles the facts. `fine`: every fact is only what it says, and an export reads
names only. `scalac`: no exports (ignored); a member lookup finds a symbol without its info.
`dotc`: an export reads the other class's member set as indexed so far if it is in progress, and
skips a member whose type is in progress; a member lookup forces the member's info. -/
inductive Cut | fine | scalac | dotc
  deriving DecidableEq, Repr

abbrev Rule (α : Type) := Task (Probe Fact) (fun _ => Value) α

def force (f : Fact) : Rule Value := .ask (.force f) .pure
def peek (f : Fact) : Rule Value := .ask (.peek f) .pure

/-- `r`'s member names as a consumer sees them. Under dotc a set in progress is read as the names
indexed so far; under the other cuts the read forces it, a cycle if it is in progress. -/
def visibleNames (cut : Cut) (p : Program) (r : Ref) : Rule (List String) := do
  let v ← if cut == .dotc then peek (.decls r) else force (.decls r)
  match v with
  | .names ns => pure ns
  | _ => pure (if cut == .dotc then ownNames p r else [])

/-- Which class declares `n`, looking up through the parents. -/
def lookupIn (cut : Cut) (p : Program) : Nat → Ref → String → Rule (Option Ref)
  | 0, _, _ => pure none
  | fuel + 1, r, n => do
    let ns ← visibleNames cut p r
    if n ∈ ns then
      if cut == .dotc then do let _ ← force (.mem r n); pure (some r)   -- dotc's `member` forces the info
      else pure (some r)
    else
      let v ← force (.info r)
      match v with
      | .parent (some par) => lookupIn cut p fuel (cls par) n
      | _ => pure none

/-- The first implicit class taking `r` that has a member `n`. -/
def findImplicit (cut : Cut) (p : Program) (r : Ref) (n : String) : List Decl → Rule (Option Ref)
  | [] => pure none
  | d :: ds => do
    if d.isImplicit && !d.obj && (d.params.head?.map (·.2) == some r.name) && !r.obj then
      let o ← lookupIn cut p p.length (cls d.name) n
      match o with
      | some o => pure (some o)
      | none => findImplicit cut p r n ds
    else findImplicit cut p r n ds

def isDeprecated (p : Program) (o : Ref) (n : String) : Bool :=
  ((findDecl p o).bind fun d => d.members.find? (·.name == n)).map (·.deprecated) == some true

/-- One step of a path: the member `n` of owner `o`, its type joined to what was reached so far. -/
def step (acc : Typed) (p : Program) (o : Ref) (n : String) (via : Option Via) (v : Value) : Typed :=
  let t := match v with | .typed t => t.ty | .err m => .err m | _ => .err "not a type"
  { ty := t, via := via <|> acc.via,
    deprecated := acc.deprecated ++ (if isDeprecated p o n then [(o, n)] else []) }

/-- The type of a path from inside `r`: the first name is a member of `r` or a top-level object,
each further name a member of the type so far, or of an implicit class taking it. -/
def walk (cut : Cut) (p : Program) : Typed → List String → Rule Value
  | acc, [] => pure (.typed acc)
  | acc, n :: rest =>
    match acc.ty with
    | .ref r => do
      let o ← lookupIn cut p p.length r n
      match o with
      | some o => do let v ← force (.mem o n); walk cut p (step acc p o n none v) rest
      | none =>
        let i ← findImplicit cut p r n p
        match i with
        | some o => do let v ← force (.mem o n); walk cut p (step acc p o n (some ⟨o.name, n, r.name⟩) v) rest
        | none => pure (.typed { acc with ty := .err s!"value {n} is not a member of {r.name}" })
    | .builtin b => pure (.typed { acc with ty := .err s!"value {n} is not a member of {b}" })
    | .err _ => pure (.typed acc)

def typePath (cut : Cut) (p : Program) (r : Ref) : List String → Rule Value
  | [] => pure (.err "empty path")
  | first :: rest => do
    let o ← lookupIn cut p p.length r first
    match o with
    | some o => do let v ← force (.mem o first); walk cut p (step { ty := .err "" } p o first none v) rest
    | none =>
      if (findDecl p (obj first)).isSome then walk cut p { ty := .ref (obj first) } rest
      else pure (ty (.err s!"not found: value {first}"))

/-- A declared type: a class of the program, or a builtin. -/
def declaredType (p : Program) (t : String) : Value :=
  if (findDecl p (cls t)).isSome then ty (.ref (cls t)) else ty (.builtin t)

/-- The class or object `export src` refers to. -/
def exportSource (p : Program) (src : String) : Ref :=
  if (findDecl p (obj src)).isSome then obj src else cls src

/-- A forwarder for each member whose type is not in progress (dotc's wildcard export). -/
def keepFinished (src : Ref) : List String → Rule (List String)
  | [] => pure []
  | n :: ns => do
    let t ← peek (.mem src n)
    let rest ← keepFinished src ns
    pure (if t == absent then rest else n :: rest)

/-- The names an export of `src` adds, under the cut: `fine` all of them (or the named ones), by
name; `dotc` the same, less the members whose types are in progress; `scalac` none. -/
def exportedNames (cut : Cut) (p : Program) (src : String) (names : Option (List String)) :
    Rule (List String) := do
  if cut == .scalac then pure []
  else
    let src := exportSource p src
    let all ← visibleNames cut p src
    let wanted := match names with | some ns => all.filter (· ∈ ns) | none => all
    if cut == .dotc then keepFinished src wanted else pure wanted

/-- Add forwarders to a member set; a name already there is a conflicting definition. -/
def addNames : List String → List String → Value
  | acc, [] => .names acc
  | acc, n :: ns => if n ∈ acc then .err s!"conflicting definitions: {n}" else addNames (acc ++ [n]) ns

def declsRule (cut : Cut) (p : Program) : List (String × Option (List String)) → List String → Rule Value
  | [], acc => pure (.names acc)
  | (src, names) :: es, acc => do
    let ns ← exportedNames cut p src names
    match addNames acc ns with
    | .names acc' => declsRule cut p es acc'
    | e => pure e

/-- The type of a member reached through an export of the class. -/
def forwardedType (cut : Cut) (p : Program) (n : String) : List (String × Option (List String)) → Rule Value
  | [] => pure (.err s!"not found: value {n}")
  | (src, names) :: es => do
    let ns ← exportedNames cut p src names
    if n ∈ ns then force (.mem (exportSource p src) n)
    else forwardedType cut p n es

/-- The namer: the rule of every fact of the program, as `cut` bundles it. -/
def rulesOf (cut : Cut) (p : Program) : PRules Fact Value
  | .info r => .pure (.parent ((findDecl p r).bind (·.parent)))
  | .decls r =>
    match findDecl p r with
    | none => .pure (.err s!"not found: {r.name}")
    | some d => declsRule cut p d.exports (ownNames p r)
  | .mem r n =>
    match findDecl p r with
    | none => .pure (.err s!"not found: {r.name}")
    | some d =>
      if n ∈ synthetics p r then
        .pure (match n with
          | "equals" => ty (.builtin "Boolean")
          | "hashCode" => ty (.builtin "Int")
          | "toString" => ty (.builtin "String")
          | _ => ty (.ref (cls r.name)))
      else match d.params.find? (·.1 == n) with
      | some (_, t) => .pure (declaredType p t)
      | none =>
        match d.members.find? (·.name == n) with
        | some m =>
          match m.declared with
          | some t => .pure (declaredType p t)
          | none => typePath cut p r m.path
        | none => forwardedType cut p n d.exports

/-! ## Demands: what typing a file in an order forces -/

/-- Typing `r`: its member names, its parent, and each source member's type. -/
def demandsOf (p : Program) (r : Ref) : List Fact :=
  [.decls r, .info r] ++ ((findDecl p r).map (·.members.map fun m => Fact.mem r m.name)).getD []

def demands (p : Program) (order : List Ref) : List Fact := order.flatMap (demandsOf p)

/-- The run of a compiler with this cut over the files in `order`: outcomes and the final store. -/
def run (cut : Cut) (p : Program) (order : List Ref) : List (Out Fact Value) × Store Fact Value :=
  forcePeekAll (rulesOf cut p) absent 40 (demands p order) (fun _ => none)

/-- The same under full taint (`Query.Interrupt.forceT`): a value computed from an `absent` is
not stored. -/
def runTainted (cut : Cut) (p : Program) (order : List Ref) : List (Out Fact Value) × Store Fact Value :=
  Query.Interrupt.forceTAll (rulesOf cut p) false absent 40 (demands p order) (fun _ => none)

/-! ## Witnesses -/

def int : Decl := { name := "Int" }

/-! ### L9: an exported member silently missing (dotc 3.9.0)

```scala
object A { export B.*; def a = 1 }      // A.scala
object B { def b = A.a + 1 }            // B.scala
```
Typed `A.scala` first, `A` has the forwarder `b`; typed `B.scala` first, it has none, and nothing is
reported ([`docs/upstream/dotc-export-order.md`](../../../docs/upstream/dotc-export-order.md) §1). -/

def l9 : Program := [int,
  { obj := true, name := "A", stats := [.export "B" none, .member { name := "a", declared := some "Int" }] },
  { obj := true, name := "B", stats := [.member { name := "b", path := ["A", "a"] }] }]

/-- **L9 by `decide`.** Under dotc's cut, `A` first: `b`'s type is asked while `A`'s member set is
in progress, finds `a` in the names indexed so far, and the forwarder is added; `B` first: `b`'s
type asks `A`'s member set, whose export peeks `b`'s type in progress and skips it, and the set
without `b` is memoized. -/
theorem l9_dotc_order_dependent :
    (run .dotc l9 [obj "A", obj "B"]).2 (.decls (obj "A")) = some (.names ["a", "b"]) ∧
    (run .dotc l9 [obj "B", obj "A"]).2 (.decls (obj "A")) = some (.names ["a"]) := by
  decide

/-- Under the fine cut an export reads names only, and both orders agree. -/
theorem l9_fine_order_free :
    (run .fine l9 [obj "A", obj "B"]).2 (.decls (obj "A")) = some (.names ["a", "b"]) ∧
    (run .fine l9 [obj "B", obj "A"]).2 (.decls (obj "A")) = some (.names ["a", "b"]) := by
  decide

/-- **Full taint repairs L9's answer and stores nothing**: in both orders the member set demanded
for `A` is `[a, b]`, because the set that skipped `b` was computed from an `absent` and not stored,
and the demand that follows recomputes it with `b` finished. The peek stays; what goes is the memo
of every value computed above it, so after the run the store holds neither `A`'s names nor `b`'s
type: the price of taint on a program with a cycle. -/
theorem l9_taint_order_free :
    (runTainted .dotc l9 [obj "A", obj "B"]).1[0]? = some (.ok (.names ["a", "b"])) ∧
    (runTainted .dotc l9 [obj "B", obj "A"]).1[3]? = some (.ok (.names ["a", "b"])) ∧
    (runTainted .dotc l9 [obj "B", obj "A"]).2 (.decls (obj "A")) = none ∧
    (runTainted .dotc l9 [obj "B", obj "A"]).2 (.mem (obj "B") "b") = none := by
  decide

/-! ### L2: mutual exports compile or not by file order (dotc 3.9.0)

```scala
object A { export B.*; def a = 1 }      // A.scala
object B { export A.a; def b = 2 }      // B.scala
```
`A.scala` first: "Conflicting definitions: def a in object A and final def a in object A".
`B.scala` first: compiles. -/

def l2 : Program := [int,
  { obj := true, name := "A", stats := [.export "B" none, .member { name := "a", declared := some "Int" }] },
  { obj := true, name := "B", stats := [.export "A" (some ["a"]), .member { name := "b", declared := some "Int" }] }]

/-- **L2 by `decide`.** `A` first: `A`'s wildcard completes `B`, whose export of `A.a` reads `A`'s
names so far and forwards `a`, so `A` imports its own `a` back: a conflict. `B` first: `B`'s export
completes `A`, whose wildcard reads `B`'s names so far (`b` only), so nothing clashes. -/
theorem l2_dotc_order_dependent :
    (run .dotc l2 [obj "A", obj "B"]).2 (.decls (obj "A")) = some (.err "conflicting definitions: a") ∧
    (run .dotc l2 [obj "B", obj "A"]).2 (.decls (obj "A")) = some (.names ["a", "b"]) ∧
    (run .dotc l2 [obj "B", obj "A"]).2 (.decls (obj "B")) = some (.names ["b", "a"]) := by
  decide

/-- Under the fine cut the two member sets ask each other: a true cycle of the names, in both
orders. A compiler that wanted both orders to agree would need a fixed point of the name sets, not
a lazier read. -/
theorem l2_fine_cycle :
    (run .fine l2 [obj "A", obj "B"]).1.head? = some (.cyc (.decls (obj "A"))) ∧
    (run .fine l2 [obj "B", obj "A"]).1.head? = some (.cyc (.decls (obj "B"))) := by
  decide

/-! ### The Java toy's scenarios -/

/-- `scenarios/cycle.toy`: `def a = b; def b = a` beside a well-founded `def p = q.c`. -/
def cycleToy : Program := [int,
  { name := "C", stats := [
      .member { name := "a", path := ["b"] }, .member { name := "b", path := ["a"] },
      .member { name := "c", declared := some "Int" },
      .member { name := "p", path := ["q", "c"] }, .member { name := "q", declared := some "C" }] }]

/-- A true cycle is a cycle under every cut, and the well-founded member beside it is typed. -/
theorem cycleToy_all_cuts :
    ∀ cut ∈ [Cut.fine, .scalac, .dotc], (run cut cycleToy [cls "C"]).2 (.mem (cls "C") "p") = some (ty (.ref (cls "Int"))) ∧
      (run cut cycleToy [cls "C"]).2 (.mem (cls "C") "a") = none := by
  decide

/-- `scenarios/implicit-class.toy`: `Use.g = three.twice` through `implicit class RichInt(i: Int)`. -/
def implicitToy : Program := [int,
  { name := "Before", stats := [.member { name := "x", declared := some "Int" }] },
  { isImplicit := true, name := "RichInt", params := [("i", "Int")], stats := [.member { name := "twice", declared := some "Int" }] },
  { obj := true, name := "Use", stats := [
      .member { name := "b", declared := some "Before" }, .member { name := "f", path := ["b", "x"] },
      .member { name := "three", declared := some "Int" }, .member { name := "g", path := ["three", "twice"] }] }]

/-- The implicit view resolves under every cut, in either file order, and the fact records the
class it went through: the identity cache that scala/scala#11328 fixes is kernel state, not a fact. -/
theorem implicitToy_order_free :
    ∀ cut ∈ [Cut.fine, .scalac, .dotc], (run cut implicitToy [cls "Before", cls "RichInt", obj "Use"]).2 (.mem (obj "Use") "g") = some (.typed { ty := .ref (cls "Int"), via := some ⟨"RichInt", "twice", "Int"⟩ }) ∧
      (run cut implicitToy [obj "Use", cls "RichInt", cls "Before"]).2 (.mem (obj "Use") "g") = some (.typed { ty := .ref (cls "Int"), via := some ⟨"RichInt", "twice", "Int"⟩ }) := by
  decide

/-- `scenarios/case-class-completion.toy`: a case class's synthetics are names the namer knows. -/
def caseToy : Program := [int,
  { isCase := true, name := "L", params := [("a", "Int")], stats := [.member { name := "self", declared := some "L" }] },
  { obj := true, name := "Use", stats := [.member { name := "l", declared := some "L" }, .member { name := "f", path := ["l", "self"] }] }]

/-- The names are facts of the namer; the burst that adds them to the scope one at a time, and the
map that moves their trees, are the kernel's state (`Query.Interrupt` §4). -/
theorem caseToy_names :
    (run .scalac caseToy [cls "L", obj "L", obj "Use"]).2 (.decls (cls "L")) = some (.names ["a", "self", "copy", "equals", "hashCode", "toString"]) ∧
    (run .scalac caseToy [cls "L", obj "L", obj "Use"]).2 (.decls (obj "L")) = some (.names ["apply", "unapply"]) := by
  decide

end ScalaTypes.ToyNamer
