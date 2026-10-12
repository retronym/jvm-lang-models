import IncComp.NonLocalAns
import Zinc.Bridges.Hier
/-!
# Flattened Merkle composition over a stored, possibly stale linearization

The Zinc PoC (decision 1) composes the per-name hash of class `C` without recursion:

    H_C(n) = hash(own_C(n), [(P as seen from C, own_P(n)) | P ∈ lin(C), n ∈ decls(P)])

where `lin(C)` is the linearization *stored at `C`'s last compile*. It goes stale when an
ancestor's parents change; the argument for soundness is that such a header change recompiles
every transitive descendant, which refreshes the stored `lin`.

The model: the language of `Hier.lean` (one type parameter, parents with a type argument) with
Scala's linearization, lowered to the shared syntax (`declToScala`). A class's compilation computes
its linearization with the shared walk over headers (`Scala.linH`, through `Task.interp`), asking
every ancestor for its `header`, and stores it in its interface; member types are seen from a
class by the shared `asSeenFrom`. `FlatShared` proves both are the shared semantics. A client selects `c.n` with one `member` query
whose answer is the lookup along `c`'s *stored* linearization, which is a function of the
flattened hash by construction. Keys:

* `(c, name n)`, hashed by the flattened composition and `c`'s kind (a trait receiver is
  `invokeinterface`), for a selection `c.n` (`client`, or `uses`
  when a class selects its own member: Zinc drops those self-references);
* `(p, parents)`, hashed by `p`'s parents, kind and finality, for every `header` query a class
  asks while linearizing (`header`). Since a class asks this of *every* ancestor, the keys say "recompile
  every transitive descendant when a parents list changes": the header rule.

A class's compilation also runs a refchecks prelude against its ancestors (PoC decision 3, talk
§10a), each check a query recorded like a client's:

* override conformance of each own member: `(p, own n)`, Zinc's decls-only name hash (`overrides`);
* inherited-member reconciliation: which ancestors declare `n` (`(p, has n)`), and for pairs
  through different parents their members (`(p, own n)`) (`conflicts`);
* abstract members of a concrete class: which ancestors declare `n` and whether deferred
  (`(p, dfr n)`) (`abstract`).

and a codegen epilogue, since a class's bytecode also derives from ancestors its source never names:

* mixin forwarders: a class (or object) asks each trait it mixes in for its declarations
  (`(t, decls)`), and the ancestors ahead of the trait whether they declare the name
  (`(q, has n)`) (`trait`);
* static forwarders: an object asks every ancestor for its declarations, for its mirror
  class (`(q, decls)`) (`mirror`);
* `final` parents and which ancestors are traits are part of the header (`(p, parents)`).

So the rule table of decision 3 is the key abstraction of the descendant's refchecks and codegen
trace, and T2″ covers the filtered inheritance edge.

`Fl_obligations` proves the full key set meets `NCompiler.Obligations`, so decision 1 is sound
(T2″, T3a″) with `Δ` over `R` and the classes whose stored linearization meets `R`. The scenarios
check the PoC's literal `Δ` domain (`R ∪ inheritance.reverse*(R)`) and the header rule as a
policy instead of keys, and show what breaks without it or with a non-transitive one.
-/

open Query IncComp

namespace Zinc.Flat

open Zinc.Hier (Cls Name Ty allCls)
open Zinc.Hier.Cls Zinc.Hier.Name

instance : Fintype Cls := ⟨allCls, by intro x; cases x <;> decide⟩

def names : List Name := [m, g]

/-- What a member is: a method, or a field with its accessors (`val`, `var`, `lazy val`). A field
of a trait is implemented in each class that mixes the trait in directly. -/
inductive Mod | dfn | val | var | lzy
  deriving DecidableEq, Repr

structure Mem where
  ty : Ty
  deferred : Bool := false
  mod : Mod := .dfn
  /-- Private: invisible to clients, descendants and the API, but a trait's private field is
  still implemented by the classes that mix it in (Zinc's `extraHash` channel). -/
  priv : Bool := false
  deriving DecidableEq, Repr

/-- What a definition is. Traits get no forwarders; a class or object gets mixin forwarders for
the traits it mixes in, and a top-level object (no companion) gets a mirror class of static
forwarders. -/
inductive CKind | cls | trt | obj
  deriving DecidableEq, Repr

structure Decl where
  parents : List (Cls × Ty) := []
  decls : List (Name × Mem) := []
  /-- An abstract class or trait need not implement its deferred members. -/
  abstract : Bool := false
  kind : CKind := .cls
  final : Bool := false
  /-- A value class's underlying type: `V` erases to it. -/
  under : Option Ty := none
  deriving DecidableEq, Repr

/-- Proper ancestors, most derived first, with type arguments as seen from the class: the shared
linearization's (`Scala.linH`). -/
abbrev Lin := List (Cls × List Scala.Ty)

structure Src where
  decl : Decl
  body : List (Cls × Name) := []
  /-- Whole-class observations, as by a macro that reads every member of its type argument. -/
  observes : List Cls := []
  deriving DecidableEq, Repr

/-- A unit: the class and its source. -/
abbrev USrc := Cls × Src

def lowerAll (src : Cls → Src) : Cls → USrc := fun c => (c, src c)

/-- The interface stores the declaration and the linearization computed when it was compiled. -/
@[ext] structure Iface where
  decl : Decl
  lin : Lin := []
  deriving DecidableEq, Repr

/-! ## Lowering to the shared syntax

The front end: a declaration of `Flat` as a `Scala.Decl`. A type parameter is the class's first;
an object has none. `Members` has no `var`: it lowers to a `def` (`FlatShared` counts those
programs apart). -/

def memToScala (self : Cls) (n : Name) (mm : Mem) : Scala.Mem :=
  { name := n.str, res := Ty.toScala self mm.ty, abs := mm.deferred, priv := mm.priv,
    isVal := mm.mod == .val || mm.mod == .lzy, lzy := mm.mod == .lzy, nullary := true }

def kindToScala : CKind → Scala.Kind
  | .cls => .cls | .trt => .trt | .obj => .obj

def tparamsOf (d : Decl) : Nat := if d.kind == .obj then 0 else 1

def parentToScala (c : Cls) : Cls × Ty → Scala.Parent := fun (p, a) => (p.name, [Ty.toScala c a])

def declToScala (c : Cls) (d : Decl) : Scala.Decl :=
  { name := c.name, kind := kindToScala d.kind, abs := d.abstract, final := d.final,
    tparams := tparamsOf d
    super := d.parents.head?.map (parentToScala c), traits := d.parents.tail.map (parentToScala c)
    members := d.decls.map fun (n, mm) => memToScala c n mm }

theorem header_declToScala (c : Cls) (d : Decl) :
    (declToScala c d).header =
      ⟨c.name, tparamsOf d, kindToScala d.kind, d.parents.map (parentToScala c)⟩ := by
  simp only [declToScala, Scala.Decl.header, Scala.Decl.parents]
  congr 1
  cases d.parents <;> rfl

/-- `c`'s own type arguments: its parameters, as the shared linearization lists `c` itself. -/
def selfArgs (c : Cls) (d : Decl) : List Scala.Ty := (List.range (tparamsOf d)).map (Scala.Ty.tp [c.name])

/-- A member type `t` declared in `o`, as seen from `c`, where `o`'s type arguments as seen from
`c` are `ts`: the shared `asSeenFrom`. -/
def seen (c o : Cls) (ts : List Scala.Ty) (t : Ty) : Scala.Ty :=
  Scala.seenFromN c.name [(o.name, ts)] o.name (Ty.toScala o t)

/-- A refchecks verdict. Errors stand in for everything a descendant's own compilation derives
from its ancestors (also bridges and forwarders in a legal program). -/
inductive Err
  | override (n : Name)
  | conflict (n : Name)
  | abstract (n : Name)
  /-- A parent is `final`. -/
  | final (p : Cls)
  deriving DecidableEq, Repr

structure Out where
  iface : Iface
  errs : List Err
  /-- The resolved and erased type of each selection, and the receiver's kind:
  `invokeinterface` for a trait, `invokevirtual` for a class. -/
  descs : List (CKind × Option Scala.Ty × Option Scala.Ty)
  /-- Mixin forwarders: a concrete trait member that the class's linearization resolves to, for
  a trait it mixes in (one not already in its superclass's linearization), as seen from it. -/
  fwds : List (Name × Scala.Ty × Scala.Ty) := []
  /-- Static forwarders of an object's mirror class: every member, resolved, as seen from it,
  and erased. -/
  statics : List (Name × Scala.Ty × Scala.Ty) := []
  /-- Fields implemented for the traits mixed in directly, private ones included. -/
  fields : List (Name × Scala.Ty × Mod × Bool) := []
  /-- Bridges: an own member whose erasure differs from that of a member it overrides. -/
  bridges : List (Name × Scala.Ty) := []
  /-- Each whole-class observation: every member of the class, resolved, as seen from it. -/
  obs : List (List (Option Scala.Ty × Option Ty)) := []
  deriving DecidableEq, Repr

/-- The public declarations: what clients, descendants and the API see. -/
def pub (d : Decl) : List (Name × Mem) := d.decls.filter fun e => !e.2.priv

/-- A definition's own member `n` as clients and descendants see it: the first declaration of
`n`, unless private (the shared `Decl.member`, without the class's own view of its privates). -/
def ownD (d : Decl) (n : Name) : Option Mem := (d.decls.lookup n).filter fun mm => !mm.priv

def own (i : Iface) (n : Name) : Option Mem := ownD i.decl n

/-- The flattened composition: `own_C(n)`, then each ancestor of the stored linearization that
declares `n`, with its type arguments as seen from `c`. -/
def flatOf (I : Cls → Iface) (c : Cls) (n : Name) : List (Cls × List Scala.Ty × Mem) :=
  ((c, selfArgs c (I c).decl) :: (I c).lin).filterMap fun e =>
    (own (I e.1) n).map fun m => (e.1, e.2, m)

/-- Lookup along the stored linearization: the first declaration, as seen from `c`. -/
def lookupFlat (c : Cls) (l : List (Cls × List Scala.Ty × Mem)) : Option Scala.Ty :=
  l.head?.map fun e => seen c e.1 e.2.1 e.2.2.ty

/-- The declared type of the member found, which erasure reads. A client's descriptor and its
unboxing depend on both. -/
def erasedFlat (l : List (Cls × List Scala.Ty × Mem)) : Option Ty :=
  l.head?.map fun e => e.2.2.ty

/-- A whole-class observation: every member, resolved, and its declared type. -/
def allFlat (I : Cls → Iface) (c : Cls) : List (Option Scala.Ty × Option Ty) :=
  names.map fun n => (lookupFlat c (flatOf I c n), erasedFlat (flatOf I c n))

/-! ## Queries -/

/-- Why a class asks for `V`'s underlying type: to erase a selection's type, a mixin
forwarder's, a static forwarder's, or an overridden member's (for bridges). -/
inductive UCtx | sel | fwd | mir | ovr
  deriving DecidableEq, Repr

inductive Q
  /-- What linearization reads: type parameters, kind, parents (`Scala.Q.header`). -/
  | header
  /-- Select member `n` of the addressed class: a lookup along its stored linearization. -/
  | member (n : Name)
  /-- Refchecks, override conformance: the addressed ancestor's own member `n`. -/
  | ovr (n : Name)
  /-- Refchecks, conflicts: does the addressed ancestor declare `n`? -/
  | has (n : Name)
  /-- Refchecks, conflicts: the own member `n` of an ancestor in a cross-parent pair. -/
  | cfl (n : Name)
  /-- Refchecks, abstract members: is the addressed ancestor's `n` deferred, if declared? -/
  | dfr (n : Name)
  /-- The rest of the header: kind and finality (final parents, which ancestors are traits). -/
  | hdr
  /-- Mixin forwarders: the declarations of a trait the class mixes in. -/
  | fwd
  /-- Mixin forwarders: does an ancestor ahead of the trait declare `n` (and so win)? -/
  | fhas (n : Name)
  /-- Static forwarders: the declarations of an ancestor of an object. -/
  | mirror
  /-- A direct parent named in the extends clause: its header and stored linearization. -/
  | ext
  /-- A whole-class observation (a macro): every member of the addressed class. -/
  | all
  /-- The addressed value class's underlying type, which erasure reads. -/
  | under (ctx : UCtx)
  deriving DecidableEq, Repr

inductive AnsV
  | header (h : Option Scala.Header)
  | ty (t : Option Ty)
  | sel (k : CKind) (t : Option Scala.Ty) (e : Option Ty)
  | ex (k : CKind) (f : Bool) (ps : List (Cls × Ty)) (l : Lin)
  | obs (k : CKind) (l : List (Option Scala.Ty × Option Ty))
  | mem (m : Option Mem)
  | b (x : Bool)
  | ob (x : Option Bool)
  | hd (k : CKind) (f : Bool)
  | ds (l : List (Name × Mem))
  deriving DecidableEq, Repr

def answer (I : Cls → Iface) : Cls × Q → AnsV
  | (c, .header) => .header (some (declToScala c (I c).decl).header)
  | (c, .member n) => .sel (I c).decl.kind (lookupFlat c (flatOf I c n)) (erasedFlat (flatOf I c n))
  | (c, .ovr n) => .mem (own (I c) n)
  | (c, .cfl n) => .mem (own (I c) n)
  | (c, .has n) => .b (own (I c) n).isSome
  | (c, .dfr n) => .ob ((own (I c) n).map (·.deferred))
  | (c, .hdr) => .hd (I c).decl.kind (I c).decl.final
  | (c, .fwd) => .ds (I c).decl.decls
  | (c, .fhas n) => .b (own (I c) n).isSome
  | (c, .mirror) => .ds (I c).decl.decls
  | (c, .ext) => .ex (I c).decl.kind (I c).decl.final (I c).decl.parents (I c).lin
  | (c, .all) => .obs (I c).decl.kind (allFlat I c)
  | (c, .under _) => .ty (I c).decl.under

abbrev T := Query.Task (Cls × Q) (fun _ => AnsV)
abbrev Env := Query.Task.Env (Cls × Q) (fun _ => AnsV)

def askQ (c : Cls) (q : Q) : T AnsV := Query.Task.ask (c, q) Query.Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Env) : (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Env) : (askQ c q).trace e = [(c, q)] := rfl

/-! ## Linearization: the shared walk

`Scala.linH` asks one `header` query per class it visits (`Scala.asks_linH`); `toQ` asks it of the
class it names, and a name that is no class of the program is not found. -/

def AnsV.hdr? : AnsV → Option Scala.Header | .header h => h | _ => none

/-- The shared layer's queries as `Flat`'s. The walk asks only `header`. -/
def toQ : (q : Scala.Q) → T (Scala.Ans q)
  | .decl .. => pure none
  | .header s => match Cls.ofName? s with
    | some c => do pure (← askQ c .header).hdr?
    | none => pure none
  | .member .. => pure none

/-- The shared linearization by class; a failed walk (too deep, a class not found) is empty. -/
def ofLin : Except String (List ((String × Scala.Header) × List Scala.Ty)) → Lin
  | .ok l => l.filterMap fun (h, ts) => (Cls.ofName? h.2.name).map (·, ts)
  | .error _ => []

/-- The linearization of `c`, whose header is `h`, `c` first. -/
def linOf (c : Cls) (h : Scala.Header) : T Lin := do
  let r ← Query.Task.interp toQ (Scala.linH Scala.fuel (c.name, h)).run
  pure (ofLin r)

/-- The linearization of `p`, `p` first, its header asked of `p`. -/
def linOfName (p : Cls) : T Lin := do
  let r ← Query.Task.interp toQ (do Scala.linH Scala.fuel (← Scala.Node.header.fetch p.name)).run
  pure (ofLin r)

/-- The classes of each parent's linearization, the parent first. -/
def parentLins : List (Cls × Ty) → T (List (List Cls))
  | [] => pure []
  | (p, _) :: rest => do
    let l ← linOfName p
    let ls ← parentLins rest
    pure (l.map (·.1) :: ls)

/-! ## Per-unit task -/

/-- The erasure of a type other than `V`: the type parameter erases to `Object`. -/
def eraseTy : Ty → Scala.Ty
  | .int => .int
  | .string => .str
  | .param => .obj
  | .v => .ref "V"

/-- Erasure: `V` erases to its underlying type if it is a value class. -/
def erase (ctx : UCtx) (t : Ty) : T Scala.Ty :=
  if t == .v then do
    match ← askQ V (.under ctx) with
    | .ty (some u) => pure (eraseTy u)
    | _ => pure (eraseTy .v)
  else pure (eraseTy t)

def eraseO (ctx : UCtx) : Option Ty → T (Option Scala.Ty)
  | some t => do pure (some (← erase ctx t))
  | none => pure none

def selects : List (Cls × Name) → T (List (CKind × Option Scala.Ty × Option Scala.Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let r ← askQ c (.member n)
    let d ← match r with
      | .sel k t e => do pure (k, t, ← eraseO .sel e)
      | _ => pure (.cls, none, none)
    let ts ← selects rest
    pure (d :: ts)

/-- Whole-class observations (macros). -/
def observe : List Cls → T (List (List (Option Scala.Ty × Option Ty)))
  | [] => pure []
  | c :: rest => do
    let r ← askQ c .all
    let os ← observe rest
    pure ((match r with | .obs _ l => l | _ => []) :: os)

/-- The extends clause: each direct parent's header and stored linearization. Zinc records it
as a `memberRef` dependency of the descendant on its parent's name. -/
def extendsClause : List (Cls × Ty) → T Unit
  | [] => pure ()
  | (p, _) :: rest => do
    let _ ← askQ p .ext
    extendsClause rest

/-! ## Refchecks

A class's own compilation reads its ancestors (talk §10a, "When a descendant must recompile
anyway"). Each check is a query to the ancestor, recorded like a client's. -/

/-- May a member of kind `k` override `m'`? A `var` cannot be overridden, a `val` only by a
`val`, and a `lazy val` only by a `lazy val` and only overrides a `lazy val` or a method. -/
def modOk (k : Mod) (m' : Mem) : Bool :=
  match m'.mod, k with
  | .var, _ => m'.deferred
  | .val, .val => true
  | .val, _ => false
  | .lzy, .lzy => true
  | .lzy, _ => false
  | .dfn, _ => true

/-- Override conformance of each own (public) member of `c` against every ancestor's member of
that name, as seen from `c`, and the bridges it needs: one per erasure of an overridden member
that differs from its own. -/
def checkOverrides (c : Cls) (ds : List (Name × Mem)) (L : Lin) :
    T (List Err × List (Name × Scala.Ty)) := do
  let mut errs := []
  let mut brs := []
  for (n, mm) in ds.filter (fun e => !e.2.priv) do
    for (p, a) in L do
      match ← askQ p (.ovr n) with
      | .mem (some m') =>
        if seen c p a m'.ty != Ty.toScala c mm.ty || !modOk mm.mod m' then errs := errs ++ [Err.override n]
        let e' ← erase .ovr m'.ty
        let e ← erase .ovr mm.ty
        if !mm.deferred && e' != e && !brs.contains (n, e') then
          brs := brs ++ [(n, e')]
      | _ => pure ()
  pure (errs, brs)

/-- Both in the linearization of one parent: the pair was checked when that parent compiled
(scalac's `OverridingPairs` skips it). -/
def sameSide (pls : List (List Cls)) (q₁ q₂ : Cls) : Bool :=
  pls.any fun l => l.contains q₁ && l.contains q₂

/-- Inherited-member reconciliation: for a name the class does not declare, find the ancestors
declaring it; for pairs coming through different parents, two concrete members conflict, and
the types (as seen from the class) must agree. -/
def checkConflicts (c : Cls) (d : Decl) (pls : List (List Cls)) (L : Lin) : T (List Err) := do
  let mut errs := []
  for n in names do
    if (ownD d n).isNone then
      let mut decl : Lin := []
      for (q, a) in L do
        if (← askQ q (.has n)) == .b true then decl := decl ++ [(q, a)]
      let cross := decl.filter fun e₁ => decl.any fun e₂ => e₁.1 != e₂.1 && !sameSide pls e₁.1 e₂.1
      let mut ms : List (Cls × Scala.Ty × Bool) := []
      for (q, a) in cross do
        match ← askQ q (.cfl n) with
        | .mem (some mm) => ms := ms ++ [(q, seen c q a mm.ty, mm.deferred)]
        | _ => pure ()
      let bad := ms.any fun e₁ => ms.any fun e₂ =>
        e₁.1 != e₂.1 && !sameSide pls e₁.1 e₂.1 && ((!e₁.2.2 && !e₂.2.2) || e₁.2.1 != e₂.2.1)
      if bad then errs := errs ++ [Err.conflict n]
  pure errs

/-- A concrete class must not be left with only deferred members of a name. A deferred
declaration in `q` overrides a concrete one in an ancestor of `q` (scalac: in
`abstract class A extends M { def m: Int }`, `A.m` hides `M.m`), while a concrete member through
another path implements it. So `n` is implemented iff some concrete declaration is not an
ancestor of a deferred one. -/
def checkAbstract (d : Decl) (L : Lin) : T (List Err) := do
  if d.abstract then return []
  let mut errs := []
  for n in names do
    match ownD d n with
    | some mm => if mm.deferred then errs := errs ++ [Err.abstract n]
    | none =>
      let mut conc : List Cls := []
      let mut dfrd : List Cls := []
      for (q, _) in L do
        match ← askQ q (.dfr n) with
        | .ob (some true) => dfrd := dfrd ++ [q]
        | .ob (some false) => conc := conc ++ [q]
        | _ => pure ()
      if !dfrd.isEmpty then
        let mut hidden : List Cls := []
        for q in dfrd do
          let lq ← linOfName q
          hidden := hidden ++ (lq.drop 1).map (·.1)
        if conc.all hidden.contains then errs := errs ++ [Err.abstract n]
  pure errs

/-! ## Code generation

A class's bytecode also derives from its ancestors without naming them in its source: mixin
forwarders (scalac's `mixin` phase) and an object's mirror class (`genBCode`). Each is a query
to the ancestor, recorded like a client's. -/

/-- The kind and finality of each class of the linearization. -/
def headers : Lin → T (List (Cls × CKind × Bool))
  | [] => pure []
  | (c, _) :: rest => do
    let h ← askQ c .hdr
    let hs ← headers rest
    pure (match h with | .hd k f => (c, k, f) :: hs | _ => hs)

def isTrait (hs : List (Cls × CKind × Bool)) (c : Cls) : Bool := hs.any fun e => e.1 == c && e.2.1 == .trt

/-- A parent may not be `final`. -/
def checkFinal (d : Decl) (hs : List (Cls × CKind × Bool)) : List Err :=
  d.parents.filterMap fun (p, _) => if hs.any (fun e => e.1 == p && e.2.2) then some (Err.final p) else none

/-- The first ancestor that declares `n`. -/
def firstDecl (n : Name) : Lin → T (Option Cls)
  | [] => pure none
  | (q, _) :: rest => do
    if (← askQ q (.fhas n)) == .b true then pure (some q) else firstDecl n rest

/-- The traits mixed in here: those not in the superclass's linearization. The superclass is
the first parent, unless that is a trait. -/
def mixins (d : Decl) (pls : List (List Cls)) (L : Lin) (hs : List (Cls × CKind × Bool)) : Lin :=
  let sup : List Cls := match d.parents, pls with
    | (p, _) :: _, l :: _ => if isTrait hs p then [] else l
    | _, _ => []
  L.filter fun e => isTrait hs e.1 && !sup.contains e.1

/-- Mixin forwarders for the public concrete members of the traits mixed in directly, and the
fields of their `val`s, `var`s and `lazy val`s, private ones included. -/
def mixinFwds (c : Cls) (d : Decl) (pls : List (List Cls)) (L : Lin) (hs : List (Cls × CKind × Bool)) :
    T (List (Name × Scala.Ty × Scala.Ty) × List (Name × Scala.Ty × Mod × Bool)) := do
  if d.kind == .trt then return ([], [])
  let mut fs := []
  let mut fl := []
  for (t, a) in mixins d pls L hs do
    match ← askQ t .fwd with
    | .ds ds =>
      for (n, mm) in ds do
        if !mm.deferred && mm.priv && mm.mod != .dfn then
          fl := fl ++ [(n, seen c t a mm.ty, mm.mod, true)]
        if !mm.deferred && !mm.priv && (ownD d n).isNone then
          if (← firstDecl n L) == some t then
            fs := fs ++ [(n, seen c t a mm.ty, ← erase .fwd mm.ty)]
            if mm.mod != .dfn then fl := fl ++ [(n, seen c t a mm.ty, mm.mod, false)]
    | _ => pure ()
  pure (fs, fl)

def staticFwds (c : Cls) (d : Decl) (L : Lin) : T (List (Name × Scala.Ty × Scala.Ty)) := do
  if d.kind != .obj then return []
  let mut seenDs : List (Cls × List Scala.Ty × List (Name × Mem)) := []
  for (q, a) in L do
    match ← askQ q .mirror with
    | .ds ds => seenDs := seenDs ++ [(q, a, ds.filter fun e => !e.2.priv)]
    | _ => pure ()
  let found := names.filterMap fun n =>
    match ownD d n with
    | some mm => some (n, Ty.toScala c mm.ty, mm.ty)
    | none => (seenDs.findSome? fun (q, a, ds) =>
        (ds.lookup n).map fun mm => (n, seen c q a mm.ty, mm.ty))
  let mut out := []
  for (n, t, dt) in found do
    out := out ++ [(n, t, ← erase .mir dt)]
  pure out

def unitF (u : USrc) : T Out := do
  let c := u.1
  let s := u.2
  let L := (← linOf c (declToScala c s.decl).header).drop 1
  let pls ← parentLins s.decl.parents
  let hs ← headers L
  extendsClause s.decl.parents
  let (e₁, brs) ← checkOverrides c s.decl.decls L
  let e₂ ← checkConflicts c s.decl pls L
  let e₃ ← checkAbstract s.decl L
  let ts ← selects s.body
  let (fs, fl) ← mixinFwds c s.decl pls L hs
  let ss ← staticFwds c s.decl L
  let os ← observe s.observes
  pure ⟨⟨s.decl, L⟩, checkFinal s.decl hs ++ e₁ ++ e₂ ++ e₃, ts, fs, ss, fl, brs, os⟩

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  /-- The header: parents, kind, finality. -/
  | parents
  /-- The ancestor's own member `n`: Zinc's decls-only name hash. -/
  | own (n : Name)
  /-- Whether the ancestor declares `n`. -/
  | has (n : Name)
  /-- Whether the ancestor declares `n`, and if so whether deferred. -/
  | dfr (n : Name)
  /-- The ancestor's declarations: a trait's for forwarders, any ancestor's for a mirror. -/
  | decls
  /-- A direct parent, as named in an extends clause: header and stored linearization. -/
  | ext
  /-- Every member of the class, as a macro observes it: non-local, like `name`. -/
  | all
  /-- A value class's underlying type. -/
  | under
  deriving DecidableEq, Repr

inductive H
  | flat (k : CKind) (l : List (Cls × List Scala.Ty × Mem))
  | ps (k : CKind) (f : Bool) (l : List (Cls × Ty))
  | ds (l : List (Name × Mem))
  | own (m : Option Mem)
  | has (b : Bool)
  | dfr (o : Option Bool)
  | ex (k : CKind) (f : Bool) (ps : List (Cls × Ty)) (l : Lin)
  | all (k : CKind) (l : List (List (Cls × List Scala.Ty × Mem)))
  | under (o : Option Ty)
  deriving DecidableEq, Repr

def π (I : Cls → Iface) (c : Cls) : K → H
  | .name n => .flat (I c).decl.kind (flatOf I c n)
  | .parents => .ps (I c).decl.kind (I c).decl.final (I c).decl.parents
  | .decls => .ds (I c).decl.decls
  | .own n => .own (own (I c) n)
  | .has n => .has (own (I c) n).isSome
  | .dfr n => .dfr ((own (I c) n).map (·.deferred))
  | .ext => .ex (I c).decl.kind (I c).decl.final (I c).decl.parents (I c).lin
  | .all => .all (I c).decl.kind (names.map (flatOf I c))
  | .under => .under (I c).decl.under

/-- The key covering a query. -/
def keyOf : Q → K
  | .header => .parents
  | .member n => .name n
  | .ovr n => .own n
  | .cfl n => .own n
  | .has n => .has n
  | .dfr n => .dfr n
  | .hdr => .parents
  | .fwd => .decls
  | .fhas n => .has n
  | .mirror => .decls
  | .ext => .ext
  | .all => .all
  | .under _ => .under

/-- Which rule of the PoC's table a recorded key stands for. -/
inductive Kind
  | client | uses | header | overrides | conflicts | abstract | «trait» | mirror
  /-- The descendant's extends clause: Zinc's `memberRef` on the parent's name. -/
  | «extends»
  /-- A macro's observation: Zinc's macro-expansion dependency. -/
  | «macro»
  /-- Codegen's erasure of a value class it never names: forwarders and bridges. -/
  | erasure
  deriving DecidableEq, Repr

def kindOf (d : Cls) : Cls × Q → Kind
  | (_, .header) => .header
  | (c, .member _) => if c = d then .uses else .client
  | (_, .ovr _) => .overrides
  | (_, .has _) => .conflicts
  | (_, .cfl _) => .conflicts
  | (_, .dfr _) => .abstract
  | (_, .hdr) => .header
  | (_, .fwd) => .trait
  | (_, .fhas _) => .trait
  | (_, .mirror) => .mirror
  | (_, .ext) => .extends
  | (_, .all) => .macro
  | (_, .under .sel) => .client
  | (_, .under _) => .erasure

/-- The extractor, recording the keys of the enabled kinds only. -/
def keys (E : Kind → Bool) (d : Cls) (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.filterMap fun q => if E (kindOf d q) then some (q.1, keyOf q.2) else none).toFinset

def hashDeps (I : Cls → Iface) (c : Cls) : Finset Cls :=
  insert c ((I c).lin.map (·.1)).toFinset

/-! ## Joint compilation -/

/-- The declarations of a group, with nothing stored: what linearization reads. -/
def declEnv (G : Finset Cls) (src : Cls → USrc) (I : Cls → Iface) : Cls → Iface :=
  fun v => if v ∈ G then ⟨(src v).2.decl, []⟩ else I v

/-- The interfaces of a group: linearizations need only the group's source declarations. -/
def matIface (G : Finset Cls) (src : Cls → USrc) (I : Cls → Iface) (u : Cls) : Iface :=
  ⟨(src u).2.decl, ((linOf (src u).1 (declToScala (src u).1 (src u).2.decl).header).run
    (answer (declEnv G src I))).drop 1⟩

def group (G : Finset Cls) (src : Cls → USrc) (I : Cls → Iface) (u : Cls) : Out :=
  (unitF (src u)).run (answer fun v => if v ∈ G then matIface G src I v else I v)

def Fl (E : Kind → Bool) : NCompiler Cls USrc Out Iface K H Q (fun _ => AnsV) where
  unit := unitF
  group := group
  iface := Out.iface
  answer := answer
  π := π
  hashDeps := hashDeps
  keys := keys E
  covers := fun _ q k => k = (q.1, keyOf q.2)

def full : Kind → Bool := fun _ => true

/-! ## Obligations -/

open Query.Task in
theorem trace_toQ (e : Env) : ∀ q', Scala.Walky q' → ∀ q ∈ (toQ q').trace e, q.2 = .header
  | .decl .., h => h.elim
  | .header s, _ => by
    intro q hq
    simp only [toQ] at hq
    split at hq
    · simp only [bind_eq, trace_bind, trace_askQ, List.mem_append, List.mem_singleton] at hq
      rcases hq with rfl | hq
      · rfl
      · exact (List.not_mem_nil hq).elim
    · exact (List.not_mem_nil hq).elim
  | .member .., _ => by intro q hq; exact (List.not_mem_nil hq).elim

/-- A computation of the shared layer that asks only `header` and `member` queries asks, through
`toQ`, only `header` queries. -/
theorem trace_interp_walky {α : Type} (x : Scala.M α) (hx : ∀ e', Scala.Asks e' Scala.Walky x)
    (e : Env) : ∀ q ∈ (Query.Task.interp toQ x.run).trace e, q.2 = .header := by
  intro q hq
  obtain ⟨q', hq', hq⟩ := (Query.Task.mem_trace_interp toQ e _ q).1 hq
  exact trace_toQ e q' (hx _ q' hq') q hq

open Query.Task in
theorem trace_linOf (e : Env) (c : Cls) (h : Scala.Header) :
    ∀ q ∈ (linOf c h).trace e, q.2 = .header := by
  intro q hq
  simp only [linOf, bind_eq, trace_bind, pure_eq, trace_pure, List.append_nil] at hq
  exact trace_interp_walky _ (fun e' => Scala.asks_linH e' _ _) e q hq

open Query.Task in
theorem trace_linOfName (e : Env) (p : Cls) : ∀ q ∈ (linOfName p).trace e, q.2 = .header := by
  intro q hq
  simp only [linOfName, bind_eq, trace_bind, pure_eq, trace_pure, List.append_nil] at hq
  exact trace_interp_walky _ (fun e' => Scala.Asks.bind (Scala.asks_fetchH e' _)
    fun h => Scala.asks_linH e' _ h) e q hq

/-- Two interface maps with the same headers give the same linearization. -/
theorem linOf_congr (I I' : Cls → Iface)
    (h : ∀ c, (declToScala c (I c).decl).header = (declToScala c (I' c).decl).header)
    (c : Cls) (hd : Scala.Header) :
    (linOf c hd).run (answer I) = (linOf c hd).run (answer I') := by
  apply Query.Task.run_congr
  intro q hq
  have := trace_linOf _ c hd q hq
  obtain ⟨c, q⟩ := q
  simp only at this
  subst this
  simp only [answer, h c]

theorem iface_unitF (u : USrc) (e : Env) :
    ((unitF u).run e).iface =
      ⟨u.2.decl, ((linOf u.1 (declToScala u.1 u.2.decl).header).run e).drop 1⟩ := by
  simp [unitF]

theorem group_iface (G : Finset Cls) (src : Cls → USrc) (I : Cls → Iface) (u : Cls) :
    (group G src I u).iface = matIface G src I u := by
  simp only [group, iface_unitF, matIface]
  congr 2
  apply linOf_congr
  intro c
  by_cases hc : c ∈ G <;> simp [hc, declEnv]

theorem Fl_comp (E : Kind → Bool) : ∀ (G : Finset Cls) (src : Cls → USrc) (I : Cls → Iface), ∀ d ∈ G,
    (Fl E).group G src I d = ((Fl E).unit (src d)).run
      ((Fl E).answer (NCompiler.override I G ((Fl E).iface ∘ (Fl E).group G src I))) := by
  intro G src I d _
  show group G src I d = (unitF (src d)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  conv_lhs => unfold group
  congr 2
  funext v
  simp only [NCompiler.override, Function.comp]
  split
  · rw [group_iface]
  · rfl

theorem flatOf_congr (I I' : Cls → Iface) (c : Cls) (n : Name)
    (h : ∀ d ∈ hashDeps I c, I d = I' d) : flatOf I c n = flatOf I' c n := by
  have hc : I c = I' c := h c (Finset.mem_insert_self _ _)
  unfold flatOf
  rw [← hc]
  apply List.filterMap_congr
  intro e he
  rw [h e.1]
  simp only [hashDeps, Finset.mem_insert, List.mem_toFinset, List.mem_map]
  rcases List.mem_cons.1 he with rfl | he
  · exact Or.inl rfl
  · exact Or.inr ⟨e, he, rfl⟩

theorem Fl_obligations : (Fl full).Obligations where
  comp := Fl_comp full
  coverage := by
    intro I d s q hq
    refine ⟨(q.1, keyOf q.2), ?_, rfl⟩
    show _ ∈ keys full d _
    simp only [keys, full, ite_true, List.mem_toFinset, List.mem_filterMap, Option.some.injEq]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro I I' k h q hc
    refine ⟨?_, hc⟩
    change k = (q.1, keyOf q.2) at hc
    subst hc
    obtain ⟨c, q⟩ := q
    change π I c (keyOf q) = π I' c (keyOf q) at h
    cases q with
    | header =>
      simp only [keyOf, π, H.ps.injEq] at h
      simp [Fl, answer, header_declToScala, tparamsOf, h]
    | member n =>
      simp only [keyOf, π, H.flat.injEq] at h
      simp [Fl, answer, h]
    | ovr n =>
      simp only [keyOf, π, H.own.injEq] at h
      simp [Fl, answer, h]
    | cfl n =>
      simp only [keyOf, π, H.own.injEq] at h
      simp [Fl, answer, h]
    | has n =>
      simp only [keyOf, π, H.has.injEq] at h
      simp [Fl, answer, h]
    | dfr n =>
      simp only [keyOf, π, H.dfr.injEq] at h
      simp [Fl, answer, h]
    | hdr =>
      simp only [keyOf, π, H.ps.injEq] at h
      simp [Fl, answer, h]
    | fwd =>
      simp only [keyOf, π, H.ds.injEq] at h
      simp [Fl, answer, h]
    | fhas n =>
      simp only [keyOf, π, H.has.injEq] at h
      simp [Fl, answer, h]
    | mirror =>
      simp only [keyOf, π, H.ds.injEq] at h
      simp [Fl, answer, h]
    | ext =>
      simp only [keyOf, π, H.ex.injEq] at h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := h
      simp [Fl, answer, h₁, h₂, h₃, h₄]
    | all =>
      simp only [keyOf, π, H.all.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      have he : ∀ n ∈ names, flatOf I c n = flatOf I' c n := by
        intro n hn
        have := List.map_inj_left.1 h₂ n hn
        exact this
      simp only [Fl, answer, allFlat, h₁]
      rw [List.map_congr_left (fun n hn => by rw [he n hn])]
    | under ctx =>
      simp only [keyOf, π, H.under.injEq] at h
      simp [Fl, answer, h]
  locality := by
    intro I I' c h k
    have hc : I c = I' c := h c (Finset.mem_insert_self _ _)
    cases k with
    | name n => simp only [Fl, π, flatOf_congr I I' c n h, hc]
    | parents => simp only [Fl, π, hc]
    | own n => simp only [Fl, π, hc]
    | has n => simp only [Fl, π, hc]
    | dfr n => simp only [Fl, π, hc]
    | decls => simp only [Fl, π, hc]
    | ext => simp only [Fl, π, hc]
    | under => simp only [Fl, π, hc]
    | all =>
      simp only [Fl, π, hc]
      congr 1
      apply List.map_congr_left
      intro n _
      exact flatOf_congr I I' c n h

/-- **Decision 1 is sound**: with every key kind recorded, any sound policy, and `Δ` over the
classes whose stored linearization meets the recompiled set, a terminating run leaves no class
dirty. -/
theorem flat_sound (S : Finset Cls) (src : Cls → USrc) (P : Compiler.Policy Cls Out K)
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out K)
    (D : Finset Cls) (hD : D ⊆ R) (hInv : (Fl full).Inv S src s D) (s' : Compiler.State Cls Out K)
    (h : (Fl full).zinc S src P fuel n R s = some s') : (Fl full).Inv S src s' ∅ :=
  (Fl full).zinc_sound Fl_obligations S src P hP fuel n R s D hD hInv s' h

/-! ## Runs -/

section runs
open Compiler (State Policy)

abbrev St := State Cls Out K

/-- Direct parents, as Zinc's `inheritance` relation records them. -/
def directParents (s : St) (d : Cls) : List Cls := (s.out d).iface.decl.parents.map (·.1)

/-- `R` and its direct children. -/
def children (s : St) (R : Finset Cls) : Finset Cls :=
  R ∪ Finset.univ.filter fun d => ∃ p ∈ directParents s d, p ∈ R

/-- `R` and its transitive descendants: `inheritance.reverse*`. -/
def descendants (s : St) (R : Finset Cls) : Finset Cls :=
  (List.range 7).foldl (fun D _ => children s D) R

/-- Where `Δ` is taken: the read sets of the proof, the PoC's `R ∪ inheritance.reverse*(R)` in the
new state (decision 2), or `R` alone. -/
inductive Dom | proof | zinc | stale

def domain (E : Kind → Bool) : Dom → Finset Cls → St → St → Finset Cls
  | .proof, R, s, _ => (Fl E).affected R s
  | .zinc, R, _, s' => descendants s' R
  | .stale, R, _, _ => R

structure Run where
  state : St
  rounds : ℕ
  compiled : Finset Cls

/-- The loop, with the policy applied *before* the stop test, as Zinc does with its inheritance
invalidation (`NCompiler.zinc` applies it after; for a sound policy this only stops later). -/
def all : List Cls := [A, B, M, C, X, Y, Z, V]

/-- Tabulate a state, so later rounds do not recompute it through the closures of earlier ones.
Extensionally the identity. -/
def memo (s : St) : St :=
  let o := all.map fun c => (c, s.out c)
  let u := all.map fun c => (c, s.U c)
  { out := fun c => match o.lookup c with | some x => x | none => s.out c
    U := fun c => match u.lookup c with | some x => x | none => s.U c }

def runF (E : Kind → Bool) (dom : Dom) (src : Cls → Src) (P : Policy Cls Out K) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let s' := memo ((Fl E).round (lowerAll src) R s)
    let I := P n R s s' ((Fl E).invalidated Finset.univ (domain E dom R s s') s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runF E dom src P fuel (n + 1) (acc ∪ R) I s'

def headerChanged (s s' : St) (p : Cls) : Bool :=
  let d := (s.out p).iface.decl
  let d' := (s'.out p).iface.decl
  d.parents != d'.parents || d.kind != d'.kind || d.final != d'.final

/-- The header rule as a policy: when a recompiled class's parents changed, recompile its
descendants, transitively or only the direct children. -/
def headerPolicy (transitive : Bool) : Policy Cls Out K := fun _ R s s' I =>
  let Hd := R.filter (headerChanged s s' · = true)
  I ∪ if transitive then descendants s' Hd else children s' Hd

def dummy : St := { out := fun _ => { iface := ⟨{}, []⟩, errs := [], descs := [] }, U := fun _ => ∅ }

def init (E : Kind → Bool) (src : Cls → Src) : St := memo ((Fl E).round (lowerAll src) Finset.univ dummy)

def clean (src : Cls → Src) : Cls → Out := group Finset.univ (lowerAll src) fun _ => ⟨{}, []⟩

structure Report where
  recompiled : List Cls
  rounds : ℕ
  clean : Bool
  deriving Repr, DecidableEq

def report (E : Kind → Bool) (dom : Dom) (P : Policy Cls Out K) (src₀ src₁ : Cls → Src)
    (R₀ : Finset Cls) : Option Report :=
  (runF E dom src₁ P 9 0 ∅ R₀ (init E src₀)).map fun r =>
    { recompiled := all.filter fun c => c ∈ r.compiled ∧ c ∉ R₀
      rounds := r.rounds
      clean := let cl := memo { out := clean src₁, U := fun _ => ∅ }
        all.all fun c => r.state.out c == cl.out c }

/-- Does no class inherit two instances of one ancestor, `M[Int]` and `M[String]`? Scala rejects
that ("illegal inheritance"); the linearization keeps the first. Each parent's stored
linearization is seen from the class through the parent's type argument (`asSeenFrom`, as the
shared walk's merge does). -/
def coherent (src : Cls → Src) : Bool :=
  let o := clean src
  all.all fun c =>
    let es := (src c).decl.parents.flatMap fun (p, a) =>
      let ta := Ty.toScala c a
      (p, [ta]) :: (o p).iface.lin.map fun (q, ts) =>
        (q, ts.map (AsSeenFrom.asf (Scala.namedWorld c.name [(p.name, [ta])]) (.this [c.name]) [p.name]))
    es.all fun e => es.all fun e' => e.1 != e'.1 || e.2 == e'.2

end runs

/-! ## Scenarios -/

def int : Mem := { ty := .int }
def str : Mem := { ty := .string }
def par : Mem := { ty := .param }
def intD : Mem := { ty := .int, deferred := true }

/-- §10a: `A[T] { m: Int; g: Int }`, `B extends A[Int]`, `C extends B with M`; clients
`X (B.m)`, `Y (C.m)`, `Z (B.g)`. -/
def base : Cls → Src
  | A => { decl := { decls := [(m, int), (g, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := { abstract := true, kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := { kind := .obj }, body := [(B, m)] }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj }, body := [(B, g)] }
  | V => { decl := {} }

/-- Edit 1: `A.m: Int → String`. -/
def edit1 : Cls → Src
  | A => { decl := { decls := [(m, str), (g, int)], abstract := true } }
  | c => base c

/-- Edit 2 base: `A.m: T`. -/
def base2 : Cls → Src
  | A => { decl := { decls := [(m, par), (g, int)], abstract := true } }
  | c => base c

/-- Edit 2: `B extends A[Int]` → `A[String]`, a header change. -/
def edit2 : Cls → Src
  | B => { decl := { parents := [(A, .string)] } }
  | c => base2 c

/-- Edit 3: the mixin `M` gains `m`. -/
def edit3 : Cls → Src
  | M => { decl := { decls := [(m, str)], abstract := true, kind := .trt } }
  | c => base c

/-- Edit 4 base: a header change two levels up. `M[T] { g: T }`, `A extends M[Int]`,
`B extends A[Int]`, `C extends B`; clients `X (B.g)`, `Y (C.g)`, `Z (B.m)`. -/
def base4 : Cls → Src
  | M => { decl := { decls := [(g, par)], abstract := true, kind := .trt } }
  | A => { decl := { parents := [(M, .int)], decls := [(m, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | C => { decl := { parents := [(B, .int)] } }
  | X => { decl := { kind := .obj }, body := [(B, g)] }
  | Y => { decl := { kind := .obj }, body := [(C, g)] }
  | Z => { decl := { kind := .obj }, body := [(B, m)] }
  | V => { decl := {} }

/-- Edit 4: `A extends M[Int]` → `M[String]`. `B`'s and `C`'s stored linearizations now say
`M[Int]`. -/
def edit4 : Cls → Src
  | A => { decl := { parents := [(M, .string)], decls := [(m, int)], abstract := true } }
  | c => base4 c

/-- Neither header keys nor the extends clause: the header rule's job is left undone. -/
def noHeader : Kind → Bool
  | .header => false
  | .extends => false
  | _ => true

/-- No header keys, but the descendant's dependency on the parent named in its extends clause. -/
def extOnly : Kind → Bool
  | .header => false
  | _ => true

def plain : Compiler.Policy Cls Out K := Compiler.Policy.plain

/-! ### Decision 1, with header keys

Edit 1 is as for the recursive Merkle design (`Hier.Mk`); Edit 3 also recompiles `C`, whose
conflict check sees the new `M.m` (below). A header change (Edits 2
and 4) costs a round more: in the round that recompiles `B` (or `A`), `Δ` recomputes the
descendants' hashes over their *stale* linearizations, so their clients only move once the
header keys have recompiled the descendants. The PoC's `Δ` domain gives the same runs as the
proof's. -/

example : report full .proof plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .proof plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .zinc plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .proof plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by native_decide
example : report full .proof plain base4 edit4 {A} = some ⟨[B, C, X, Y], 3, true⟩ := by native_decide
example : report full .zinc plain base4 edit4 {A} = some ⟨[B, C, X, Y], 3, true⟩ := by native_decide

/-- Decision 2 still matters: `Δ` over the recompiled set alone undercompiles (T2-stale). -/
example : report full .stale plain base edit1 {A} = some ⟨[], 1, false⟩ := by native_decide

/-! ### The header rule as a policy

Drop the header keys and enforce the rule as a policy instead. Transitive (all of
`inheritance.reverse*`) gives the same runs as the keys. Without it, or with direct children
only, the stored linearization of a grandchild stays stale: in Edit 4, `C` still says `M[Int]`
and so does its client `Y`. -/

example : report noHeader .zinc plain base4 edit4 {A} = some ⟨[], 1, false⟩ := by native_decide
example : report noHeader .zinc (headerPolicy true) base4 edit4 {A} =
    some ⟨[B, C, X, Y], 3, true⟩ := by native_decide
example : report noHeader .zinc (headerPolicy false) base4 edit4 {A} =
    some ⟨[B, X], 3, false⟩ := by native_decide
example : report noHeader .zinc plain base2 edit2 {B} = some ⟨[X, Z], 2, false⟩ := by native_decide
example : report noHeader .zinc (headerPolicy true) base2 edit2 {B} =
    some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide

/-! ### Descendants' own checks (talk §10a, "When a descendant must recompile anyway")

The refchecks keys make the inheritance edge name-filtered, and T2″ covers it. Edit 1 recompiles
no descendant (above). Each check's edit recompiles the descendant that runs it, and no other: -/

/-- `B` overrides `m`. -/
def baseO : Cls → Src
  | B => { decl := { parents := [(A, .int)], decls := [(m, int)] } }
  | c => base c

/-- Override: `A.m: Int → String`; `B.m: Int` no longer conforms. `C` inherits `m` from `B` and
`A`, through one parent, so it does not recheck the pair. -/
def editO : Cls → Src
  | A => (edit1 A)
  | c => baseO c

example : report full .zinc plain baseO editO {A} = some ⟨[B, X, Y], 2, true⟩ := by native_decide

/-- `trait M { def m: Int }`; `A.m` implements it in `C`. -/
def baseC : Cls → Src
  | M => { decl := { decls := [(m, intD)], abstract := true, kind := .trt } }
  | c => base c

/-- Conflict through two parents: `A.m: Int → String` no longer matches `M.m: Int` in `C`. `B`
sees only `A.m`. -/
def editC : Cls → Src
  | A => edit1 A
  | c => baseC c

example : report full .zinc plain baseC editC {A} = some ⟨[C, X, Y], 2, true⟩ := by native_decide

/-- Abstract: `A.m` becomes deferred; the concrete `B` and `C` must implement it. -/
def editA : Cls → Src
  | A => { decl := { decls := [(m, intD), (g, int)], abstract := true } }
  | c => base c

example : report full .zinc plain base editA {A} = some ⟨[B, C, X, Y], 2, true⟩ := by native_decide

/-- `B` selects its own inherited `m` (`this.m`). -/
def baseU : Cls → Src
  | B => { decl := { parents := [(A, .int)] }, body := [(B, m)] }
  | c => base c

def editU : Cls → Src
  | A => edit1 A
  | c => baseU c

example : report full .zinc plain baseU editU {A} = some ⟨[B, X, Y], 2, true⟩ := by native_decide

/-! ### Ablation: every key kind is needed

Dropping one kind of key leaves a scenario unclean. (Dropping `client` keys is T2-stale's
cousin: nothing reaches `X` and `Y`.) -/

def without (k : Kind) : Kind → Bool := fun k' => k' != k

example : report (without .client) .zinc plain base edit1 {A} = some ⟨[], 1, false⟩ := by native_decide
example : report (without .uses) .zinc plain baseU editU {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
example : report noHeader .zinc plain base4 edit4 {A} = some ⟨[], 1, false⟩ := by
  native_decide
example : report (without .overrides) .zinc plain baseO editO {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
/-- Edit 3's new `M.m` is also seen by the concrete `C`'s abstract check, which asks every
ancestor whether it declares `m`; the conflict keys are needed for a type mismatch. -/
example : report (without .conflicts) .zinc plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by
  native_decide
example : report (without .conflicts) .zinc plain baseC editC {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
example : report (without .abstract) .zinc plain base editA {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide

/-! ### Codegen: forwarders and `final`

`trait M[T] { def g: Int = … }` is mixed into `C`, which gets a forwarder for `g`; the object
`X extends C[Int]` gets a static forwarder for it in its mirror class. Nobody selects `g`. -/

def baseF : Cls → Src
  | A => { decl := { decls := [(m, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := { decls := [(g, int)], abstract := true, kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := { kind := .obj, parents := [(C, .int)] } }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj } }
  | V => { decl := {} }

/-- `M.g: Int → String`: both forwarders change, and no presence or client key sees it. -/
def editF : Cls → Src
  | M => { decl := { decls := [(g, str)], abstract := true, kind := .trt } }
  | c => baseF c

/-- `B` becomes `final`: `C` must fail. -/
def editFinal : Cls → Src
  | B => { decl := { parents := [(A, .int)], final := true } }
  | c => baseF c

example : report full .zinc plain baseF editF {M} = some ⟨[C, X], 2, true⟩ := by native_decide
example : report (without .trait) .zinc plain baseF editF {M} = some ⟨[X], 2, false⟩ := by
  native_decide
example : report (without .mirror) .zinc plain baseF editF {M} = some ⟨[C], 2, false⟩ := by
  native_decide
example : report full .zinc plain baseF editFinal {B} = some ⟨[C, X], 2, true⟩ := by native_decide
example : report noHeader .zinc plain baseF editFinal {B} = some ⟨[], 1, false⟩ := by
  native_decide

/-! ### The extends clause subsumes the header keys

A descendant depends on the parent its extends clause names (`ext`, Zinc's `memberRef` on the
parent's name), hashed by the parent's header *and stored linearization*. A header change then
recompiles the direct children; their linearizations change, which recompiles theirs, and so on:
the header rule's transitive closure, one round per level. -/

example : report extOnly .zinc plain base4 edit4 {A} = some ⟨[B, C, X, Y], 4, true⟩ := by
  native_decide
example : report extOnly .zinc plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by
  native_decide
example : report extOnly .zinc plain baseF editFinal {B} = some ⟨[C], 2, true⟩ := by
  native_decide

/-! ### Trait fields, erasure and whole-class observation -/

/-- `trait M { private val g: Int }` mixed into `C`; the client `Y` selects `C.m`, and `Z`
observes all of `C` (a macro). -/
def baseP : Cls → Src
  | M => { decl := { decls := [(g, { ty := .int, mod := .val, priv := true })], abstract := true,
                     kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | B => { decl := { parents := [(A, .int)] } }
  | A => { decl := { decls := [(m, int)], abstract := true } }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj }, observes := [C] }
  | _ => { decl := { kind := .obj } }

/-- The private field changes type: no name moves, but `C` implements the field. -/
def editP : Cls → Src
  | M => { decl := { decls := [(g, { ty := .string, mod := .val, priv := true })],
                     abstract := true, kind := .trt } }
  | c => baseP c

example : ((clean editP) C).fields = [(g, .str, .val, true)] := by native_decide
example : report full .zinc plain baseP editP {M} = some ⟨[C], 2, true⟩ := by native_decide
example : report (without .trait) .zinc plain baseP editP {M} = some ⟨[], 1, false⟩ := by
  native_decide

/-- `A` gains `g`, which nobody selects; the macro in `Z` sees it through `C`. -/
def editW : Cls → Src
  | A => { decl := { decls := [(m, int), (g, str)], abstract := true } }
  | c => baseP c

example : report full .zinc plain baseP editW {A} = some ⟨[B, C, Z], 2, true⟩ := by native_decide
example : report (without .macro) .zinc plain baseP editW {A} = some ⟨[B, C], 2, false⟩ := by
  native_decide

/-- `trait M[T] { def m: Int }`, `A extends M[Int]`, `B extends A { def m: Int }`. -/
def baseBr : Cls → Src
  | M => { decl := { decls := [(m, int)], abstract := true, kind := .trt } }
  | A => { decl := { parents := [(M, .int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)], decls := [(m, int)] } }
  | _ => { decl := { kind := .obj } }

/-- `M.m: T`: as seen from `A` still `Int`, but `B` now needs a bridge `m(): Object`. This is
the baseline's undercompilation (`erasure-bridge-upstream-grandparent`): the materialised design
hashes `m` as seen from `A`, which did not move. -/
def editBr : Cls → Src
  | M => { decl := { decls := [(m, par)], abstract := true, kind := .trt } }
  | c => baseBr c

example : ((clean editBr) B).bridges = [(m, .obj)] := by native_decide
example : report full .zinc plain baseBr editBr {M} = some ⟨[A, B], 2, true⟩ := by native_decide
example : report (without .overrides) .zinc plain baseBr editBr {M} = some ⟨[A], 2, false⟩ := by
  native_decide

/-! ### Value classes: erasure through a class nobody names

`V` is a value class over `Int`; `A.m` and the trait `M.g` are typed `V`; `C extends B with M`
gets a mixin forwarder for `g`, and `object X extends C` a mirror class with static forwarders
for `m` and `g`. Neither `C` nor `X` names `V`, but their bytecode erases it. -/

def vt : Mem := { ty := .v }

def baseV : Cls → Src
  | V => { decl := { under := some .int } }
  | A => { decl := { decls := [(m, vt)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := { decls := [(g, vt)], abstract := true, kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := { kind := .obj, parents := [(C, .int)] } }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj } }

/-- `V` now wraps a `String`. -/
def editV : Cls → Src
  | V => { decl := { under := some .string } }
  | c => baseV c

example : ((clean editV) C).fwds = [(g, .ref "V", .str)] := by native_decide
example : ((clean editV) X).statics = [(m, .ref "V", .str), (g, .ref "V", .str)] := by native_decide
example : report full .zinc plain baseV editV {V} = some ⟨[C, X, Y], 2, true⟩ := by native_decide

/-- Without the erasure keys only the client `Y` recompiles: `C`'s forwarder and `X`'s static
forwarders keep the old erasure. These are the baseline's and the PoC's
`value-class-mixin-forwarder` and `value-class-mirror-forwarder`. -/
example : report (without .erasure) .zinc plain baseV editV {V} = some ⟨[Y], 2, false⟩ := by
  native_decide

end Zinc.Flat
