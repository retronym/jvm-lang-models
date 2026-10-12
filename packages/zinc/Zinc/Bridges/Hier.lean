import IncComp.Termination
import IncComp.NonLocal
import ScalaTypes.Fine
import Query.Interp
/-!
# Members vs decls vs Merkle, on a toy class hierarchy

Classes with one type parameter, parents with a type argument (`asSeenFrom`), declared members,
and clients that select members. The programs are written in a small syntax (`Cls`, `Name`, `Ty`,
`Decl`, `Src`) so that they can be enumerated, and lowered to the shared Scala syntax
(`Scala.Decl`); interfaces hold the shared declaration. Member lookup *is* the shared one,
`Scala.lookupH`: Scala's linearization (each class once, the last mixin first) and the first member
named `n` along it, viewed from the class, asking one `header` query per class visited and one
`member` query per class until the first hit. `toQ` maps those queries to `Hier`'s, asked of the
class they name. `HierShared` proves this is the shared lookup over whole declarations.

Three ways to hash an inherited member, as three `Compiler` instances over the same language:

* **decls + walk** (`D`): the client's compilation performs the walk, one query per class visited;
  keys are local, interfaces are source-determined (`Model.lean`).
* **materialised members** (`W`, today's `ExtractAPI`): a class's own compilation performs the
  walk for each of its members and stores the result in its interface; the client asks one
  `members` query. Interfaces are not source-determined, so a class records inheritance keys
  (`top`) on its parents and recompiles when they change (`Model.lean`).
* **Merkle** (`Mk`): the client's compilation performs the walk, but records one key per
  *receiver*; the hash of `(C, m)` is the verifying trace of the walk from `C` for `m`, computed
  from the current interfaces without compiling anything (`NonLocal.lean`).

Zinc's hierarchy walk at invalidation time (`invalidateByInheritance` + `memberRef` of every
inheritor) is a `Policy` for `W` (`walkPolicy`).
`W` renders members *as seen from* the class, as the Scala 2 bridge does. Scala 3 renders them
*as declared* in their owner and keeps the type arguments only in `parents` (the class-name key).
On the `asSeenFrom` edit below, Scala 3's per-name hashes don't move; the class-name key moves
every client of `B`, as `D`'s `(B, parents)` key does. `Erasure.lean` compares the two renderings
and shows that only the declared one determines erasure.
-/

open Query IncComp

namespace Zinc.Hier

/-- `V` is used only by `Flat`, as a value class whose underlying type decides erasure. -/
inductive Cls | A | B | M | C | X | Y | Z | V
  deriving DecidableEq, Repr

def allCls : Finset Cls := {.A, .B, .M, .C, .X, .Y, .Z, .V}

inductive Name | m | g
  deriving DecidableEq, Repr

/-- Types: `param` is the enclosing class's single type parameter; `v` is the class `V`. -/
inductive Ty | int | string | param | v
  deriving DecidableEq, Repr

structure Decl where
  parents : List (Cls × Ty) := []
  decls : List (Name × Ty) := []
  deriving DecidableEq, Repr

structure Src where
  decl : Decl
  body : List (Cls × Name) := []
  deriving DecidableEq, Repr

/-! ## Lowering to the shared syntax -/

def Cls.name : Cls → String
  | .A => "A" | .B => "B" | .M => "M" | .C => "C" | .X => "X" | .Y => "Y" | .Z => "Z" | .V => "V"

def Cls.all : List Cls := [.A, .B, .M, .C, .X, .Y, .Z, .V]

/-- The class a name denotes, if any. -/
def Cls.ofName? (s : String) : Option Cls := Cls.all.find? (·.name = s)

def Name.str : Name → String
  | .m => "m" | .g => "g"

/-- A type of `Hier`, written in class `self`: the parameter is `self`'s first. -/
def Ty.toScala (self : Cls) : Ty → Scala.Ty
  | .int => .int
  | .string => .str
  | .param => .tp [self.name] 0
  | .v => .ref "V"

/-- A declaration of class `c`, in the shared syntax. A parent's type argument is written in the
child's scope. -/
def Decl.toScala (c : Cls) (d : Decl) : Scala.Decl :=
  let parent : Cls × Ty → Scala.Parent := fun (p, a) => (p.name, [Ty.toScala c a])
  { name := c.name
    tparams := 1
    super := d.parents.head?.map parent
    traits := d.parents.tail.map parent
    members := d.decls.map fun (n, t) => { name := n.str, res := Ty.toScala c t } }

/-- A unit's source in the shared syntax: its declaration and the selections it makes. -/
structure USrc where
  decl : Scala.Decl
  body : List (Cls × Name) := []
  deriving DecidableEq, Repr

def Src.lower (c : Cls) (s : Src) : USrc := ⟨Decl.toScala c s.decl, s.body⟩

/-- A program's sources, lowered. -/
def lowerAll (src : Cls → Src) : Cls → USrc := fun c => (src c).lower c

/-- An interface: the declaration, plus (for `W`) the materialised members. -/
@[ext] structure Iface where
  decl : Scala.Decl
  mems : List (Name × Option Scala.Ty) := []
  deriving DecidableEq, Repr

structure Out where
  iface : Iface
  /-- The resolved type of each selected member: what the client's bytecode would link against. -/
  descs : List (Option Scala.Ty)
  deriving DecidableEq, Repr

/-! ## Queries -/

inductive Q
  /-- What linearization reads: type parameters, kind, parents (`Scala.Q.header`). -/
  | header
  /-- The class's own member named `m` (`Scala.Q.member`). -/
  | member (m : String)
  | members (n : Name)
  /-- A marker: "resolution of `n` starts here". Trivial answer; it names the receiver. -/
  | select (n : Name)
  deriving DecidableEq, Repr

inductive AnsV
  | hdr (h : Option Scala.Header)
  | mem (m : Option Scala.Mem)
  | ty (t : Option Scala.Ty)
  | unit
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := AnsV

def answer (i : Iface) : Q → AnsV
  | .header => .hdr (some i.decl.header)
  | .member m => .mem (i.decl.member m)
  | .members n => .ty (((i.mems.filter (·.1.str = n.str)).head?).bind (·.2))
  | .select _ => .unit

abbrev T := Query.Task (Cls × Q) (fun p => Ans p.2)
abbrev Env := Query.Task.Env (Cls × Q) (fun p => Ans p.2)

def envOfI (I : Cls → Iface) : Env := fun p => answer (I p.1) p.2

def askQ (c : Cls) (q : Q) : T AnsV := Query.Task.ask (c, q) Query.Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Env) : (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Env) : (askQ c q).trace e = [(c, q)] := rfl

/-! ## The walk: the shared lookup

`Scala.lookupH` asks `header` and `member` queries of classes by name (`Scala.asks_lookupH`).
`toQ` asks each of the class it names; a name that is no class of the program is not found. -/

def AnsV.hdr? : AnsV → Option Scala.Header | .hdr h => h | _ => none
def AnsV.mem? : AnsV → Option Scala.Mem | .mem m => m | _ => none

/-- The shared layer's queries as `Hier`'s. -/
def toQ : (q : Scala.Q) → T (Scala.Ans q)
  | .decl .. => pure none
  | .header s => match Cls.ofName? s with
    | some c => do pure (← askQ c .header).hdr?
    | none => pure none
  | .member s m => match Cls.ofName? s with
    | some c => do pure (← askQ c (.member m)).mem?
    | none => pure none

/-- A class's own compilation answers its own `header` and `member` queries from its source. -/
def toQFrom (d : Scala.Decl) : (q : Scala.Q) → T (Scala.Ans q)
  | .header s => if s = d.name then pure (some d.header) else toQ (.header s)
  | .member s m => if s = d.name then pure (d.member m) else toQ (.member s m)
  | .decl .. => pure none

/-- A failed lookup (a class not found, a linearization too deep) selects nothing. -/
def ofExcept : Except String (Option Scala.Ty) → Option Scala.Ty
  | .ok t => t
  | .error _ => none

def fuel : ℕ := Scala.fuel

/-- Resolve member `n` of `c`, as seen from `c`: the shared lookup. -/
def resolve (c : Cls) (n : Name) : T (Option Scala.Ty) := do
  let r ← Query.Task.interp toQ (Scala.lookupH fuel c.name n.str).run
  pure (ofExcept r)

/-! ## Per-unit tasks -/

/-- Walk-based client: marker, then the walk. -/
def selects : List (Cls × Name) → T (List (Option Scala.Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let _ ← askQ c (.select n)
    let t ← resolve c n
    let ts ← selects rest
    pure (t :: ts)

def unitWalk (s : USrc) : T Out := do
  let ts ← selects s.body
  pure ⟨⟨s.decl, []⟩, ts⟩

/-- Materialise one member of a class: the shared lookup from the class, its own header and
members read from its source. -/
def resolveFrom (d : Scala.Decl) (n : Name) : T (Option Scala.Ty) := do
  let r ← Query.Task.interp (toQFrom d) (Scala.lookupH fuel d.name n.str).run
  pure (ofExcept r)

def selectsMat : List (Cls × Name) → T (List (Option Scala.Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let r ← askQ c (.members n)
    let ts ← selectsMat rest
    pure ((match r with | .ty t => t | _ => none) :: ts)

/-- Materialised: a class computes its members' resolved types (querying its ancestors' headers
and members) and stores them; clients ask `members`. -/
def unitMat (s : USrc) : T Out := do
  let mm ← resolveFrom s.decl .m
  let mg ← resolveFrom s.decl .g
  let ts ← selectsMat s.body
  pure ⟨⟨s.decl, [(.m, mm), (.g, mg)]⟩, ts⟩

/-! ## Keys -/

inductive K
  /-- Everything about the name `m` a class declares or materialises. -/
  | name (m : String)
  | parents
  /-- The whole interface: the inheritance edge. -/
  | top
  deriving DecidableEq, Repr

/-- The local key a query is covered by, for `D`. -/
def Q.keyD : Q → K
  | .header => .parents
  | .member m => .name m
  | .members n => .name n.str
  | .select n => .name n.str

/-- Decls + walk: one local key per query. -/
def keysD (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map fun p => (p.1, p.2.keyD)).toFinset

/-- Materialised: `members` by name, everything else is an inheritance edge. -/
def keysW (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map fun p => (p.1, match p.2 with
    | .members n => K.name n.str
    | _ => K.top)).toFinset

/-- Merkle: one key per receiver and name. -/
def keysM (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.filterMap fun p => match p.2 with
    | .select n => some (p.1, K.name n.str)
    | _ => none).toFinset

/-! ## Hashes (perfect: the projected data itself) -/

inductive H
  | name (mem : Option Scala.Mem) (mems : List (Name × Option Scala.Ty))
  | header (h : Scala.Header)
  | all (i : Iface)
  deriving DecidableEq, Repr

def πD (i : Iface) : K → H
  | .name m => .name (i.decl.member m) (i.mems.filter (·.1.str = m))
  | .parents => .header i.decl.header
  | .top => .all i

def πW (i : Iface) : K → H
  | .name m => .name none (i.mems.filter (·.1.str = m))
  | .parents => .header i.decl.header
  | .top => .all i

inductive CoversD : Q → K → Prop
  | header : CoversD .header .parents
  | member (m) : CoversD (.member m) (.name m)
  | select (n) : CoversD (.select n) (.name n.str)
  | members (n) : CoversD (.members n) (.name n.str)

inductive CoversW : Q → K → Prop
  | members (n) : CoversW (.members n) (.name n.str)
  | top (q) : CoversW q .top

/-- Joint compilation for source-determined interfaces (`D`, `Mk`). -/
def groupSrc (unit : USrc → T Out) (G : Finset Cls) (src : Cls → USrc) (e : Env) : Cls → Out :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then answer ⟨(src p.1).decl, []⟩ p.2 else e p

/-- Joint compilation for materialised interfaces: members are first materialised against the
group's source declarations, then clients are compiled against the materialised interfaces. -/
def matEnv (G : Finset Cls) (src : Cls → USrc) (e : Env) : Env :=
  fun p => if p.1 ∈ G then answer ⟨(src p.1).decl, []⟩ p.2 else e p

def matIface (G : Finset Cls) (src : Cls → USrc) (e : Env) (p : Cls) : Iface :=
  ((unitMat (src p)).run (matEnv G src e)).iface

def groupMat (G : Finset Cls) (src : Cls → USrc) (e : Env) : Cls → Out :=
  fun u => (unitMat (src u)).run fun p => if p.1 ∈ G then answer (matIface G src e p.1) p.2 else e p

def D : Compiler Cls USrc Out Iface K H Q Ans where
  unit := unitWalk
  group := groupSrc unitWalk
  iface := Out.iface
  answer := answer
  π := πD
  keys := keysD
  covers := CoversD

def W : Compiler Cls USrc Out Iface K H Q Ans where
  unit := unitMat
  group := groupMat
  iface := Out.iface
  answer := answer
  π := πW
  keys := keysW
  covers := CoversW

def Name.ofStr? : String → Option Name
  | "m" => some .m
  | "g" => some .g
  | _ => none

@[simp] theorem Name.ofStr?_str (n : Name) : Name.ofStr? n.str = some n := by cases n <;> rfl

/-- The Merkle hash of `(c, m)`: the verifying trace of the walk, computed from the interfaces. -/
abbrev HashM := List ((Cls × Q) × AnsV)

def πM (I : Cls → Iface) (c : Cls) : K → HashM
  | .name s => match Name.ofStr? s with
    | some n => ((resolve c n).trace (envOfI I)).map fun q => (q, envOfI I q)
    | none => []
  | _ => []

def CoversM (I : Cls → Iface) (q : Cls × Q) (k : Cls × K) : Prop :=
  ∃ n, k.2 = K.name n.str ∧ (q = (k.1, .select n) ∨ q ∈ (resolve k.1 n).trace (envOfI I))

def Mk : GCompiler Cls USrc Out Iface K HashM Q Ans where
  unit := unitWalk
  group := groupSrc unitWalk
  iface := Out.iface
  answer := answer
  π := πM
  hashDeps := fun _ => allCls
  hashRevDeps := fun _ => allCls
  keys := keysM
  covers := CoversM

/-! ## Loops that count rounds -/

section loops
variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable [DecidableEq CUnit] [DecidableEq K] [DecidableEq Hash]

/-- Result of a run: final state, number of rounds, every unit compiled in any round. -/
structure Run (CUnit Out K : Type) where
  state : Compiler.State CUnit Out K
  rounds : ℕ
  compiled : Finset CUnit

def runL (C : Compiler CUnit Src Out Iface K Hash Q A) (S : Finset CUnit) (src : CUnit → Src)
    (P : Compiler.Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → Finset CUnit → Compiler.State CUnit Out K → Option (Run CUnit Out K)
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runL C S src P fuel (n + 1) (acc ∪ R) (P n R s s' I) s'

/-- The non-local loop: `Δ` over `affected R` (or, if `stale`, over `R` only), plain policy. -/
def runG (C : GCompiler CUnit Src Out Iface K Hash Q A) (S : Finset CUnit) (src : CUnit → Src)
    (stale : Bool) :
    ℕ → ℕ → Finset CUnit → Finset CUnit → Compiler.State CUnit Out K → Option (Run CUnit Out K)
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S (if stale then R else C.affected R) s s'
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runG C S src stale fuel (n + 1) (acc ∪ R) I s'
end loops

/-! ## Zinc's hierarchy walk as a policy for `W` -/

/-- Transitive inheritors of `R`, read off the recorded `top` keys. -/
def descendants (s : Compiler.State Cls Out K) (R : Finset Cls) : Finset Cls :=
  (List.range 8).foldl (fun D _ => D ∪ allCls.filter fun d => ∃ k ∈ s.U d, k.2 = K.top ∧ k.1 ∈ D) R

/-- Did the name hash of `k` change on `p` in the round from `s` to `s'`? -/
def changedName (s s' : Compiler.State Cls Out K) (p : Cls) : K → Bool
  | .name n => decide (πW (s.out p).iface (.name n) ≠ πW (s'.out p).iface (.name n))
  | _ => false

/-- `invalidateClassesInternally`: the `memberRef` clients of every inheritor of a changed class,
filtered by the changed class's *own* changed names. -/
def walkPolicy : Compiler.Policy Cls Out K := fun _ R s s' I =>
  I ∪ allCls.filter fun e => ∃ k ∈ s'.U e, k.1 ∈ descendants s' R ∧
    ∃ p ∈ R, changedName s s' p k.2 = true

theorem walkPolicy_sound : walkPolicy.Sound allCls :=
  fun _ _ _ _ _ _ => Finset.sdiff_subset.trans Finset.subset_union_left

/-! ## Scenarios -/

open Cls Name

def base : Cls → Src
  | A => { decl := { decls := [(m, .int), (g, .int)] } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := {} }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := {}, body := [(B, m)] }
  | Y => { decl := {}, body := [(C, m)] }
  | Z => { decl := {}, body := [(B, g)] }
  | V => { decl := {} }

/-- Scenario 1: an inherited member's type changes. -/
def edit1 : Cls → Src
  | A => { decl := { decls := [(m, .string), (g, .int)] } }
  | c => base c

/-- Scenario 2 base: `A.m : T`, so `B.m` is `Int` through `B extends A[Int]`. -/
def base2 : Cls → Src
  | A => { decl := { decls := [(m, .param), (g, .int)] } }
  | c => base c

/-- Scenario 2: `B extends A[Int]` becomes `B extends A[String]`. -/
def edit2 : Cls → Src
  | B => { decl := { parents := [(A, .string)] } }
  | c => base2 c

/-- Scenario 3: the mixin `M` gains an override of `m`. -/
def edit3 : Cls → Src
  | M => { decl := { decls := [(m, .string)] } }
  | c => base c

def dummy : Compiler.State Cls Out K :=
  { out := fun _ => ⟨⟨{ name := "" }, []⟩, []⟩, U := fun _ => ∅ }

def initL (C : Compiler Cls USrc Out Iface K H Q Ans) (src : Cls → Src) :=
  C.round (lowerAll src) allCls dummy
def initG (src : Cls → Src) := Mk.round (lowerAll src) allCls dummy

/-- Everything we want to know about a run: the invalidated clients (units recompiled after
round 0), the number of rounds, and whether the result is the clean build. -/
structure Report where
  recompiled : List Cls
  rounds : ℕ
  clean : Bool
  deriving Repr, DecidableEq

def all : List Cls := [A, B, M, C, X, Y, Z]

def reportL (Cp : Compiler Cls USrc Out Iface K H Q Ans) (P : Compiler.Policy Cls Out K)
    (src₀ src₁ : Cls → Src) (R₀ : Finset Cls) : Option Report :=
  let s₀ := initL Cp src₀
  (runL Cp allCls (lowerAll src₁) P 9 0 ∅ R₀ s₀).map fun r =>
    { recompiled := all.filter fun c => c ∈ r.compiled ∧ c ∉ R₀
      rounds := r.rounds
      clean := all.all fun c => r.state.out c == (Cp.cleanFrom allCls (lowerAll src₁) s₀) c }

def reportG (stale : Bool) (src₀ src₁ : Cls → Src) (R₀ : Finset Cls) : Option Report :=
  let s₀ := initG src₀
  (runG Mk allCls (lowerAll src₁) stale 9 0 ∅ R₀ s₀).map fun r =>
    { recompiled := all.filter fun c => c ∈ r.compiled ∧ c ∉ R₀
      rounds := r.rounds
      clean := all.all fun c =>
        r.state.out c == (groupSrc unitWalk allCls (lowerAll src₁) (Mk.env s₀)) c }


/-! ### Scenario 1: `A.m : Int → String`; clients `X (B.m)`, `Y (C.m)`, `Z (B.g)`

Decls and Merkle recompile the two clients in two rounds. Materialised members recompile the
hierarchy (`B`, `C`) first, to refresh their interfaces, and reach the clients one round later;
Zinc's walk policy pulls the clients into the same round. A Merkle hash diffed over the recompiled
set only misses the clients entirely. -/

example : reportL D Compiler.Policy.plain base edit1 {A} =
    some ⟨[X, Y], 2, true⟩ := by native_decide
example : reportL W Compiler.Policy.plain base edit1 {A} =
    some ⟨[B, C, X, Y], 3, true⟩ := by native_decide
example : reportL W walkPolicy base edit1 {A} =
    some ⟨[B, C, X, Y], 2, true⟩ := by native_decide
example : reportG false base edit1 {A} =
    some ⟨[X, Y], 2, true⟩ := by native_decide
example : reportG true base edit1 {A} =
    some ⟨[], 1, false⟩ := by native_decide

/-! ### Scenario 2: `asSeenFrom`, `B extends A[Int]` → `A[String]`, with `A.m : T`, `A.g : Int`

Materialised members are the most precise: only the names whose rendering changed move, so
`Z (B.g)` stays. Decls (through the `(B, parents)` key) and the Merkle chain (parents and their
arguments are in the hash) both recompile `Z`. This is §10's precision ladder, computed. -/

example : reportL D Compiler.Policy.plain base2 edit2 {B} =
    some ⟨[X, Y, Z], 2, true⟩ := by native_decide
example : reportL W Compiler.Policy.plain base2 edit2 {B} =
    some ⟨[C, X, Y], 3, true⟩ := by native_decide
example : reportL W walkPolicy base2 edit2 {B} =
    some ⟨[C, X, Y], 2, true⟩ := by native_decide
example : reportG false base2 edit2 {B} =
    some ⟨[X, Y, Z], 2, true⟩ := by native_decide

/-! ### Scenario 3: linearization, the mixin `M` gains an override of `m`

`Y (C.m)` now resolves to `M.m`. Decls catch it through the recorded *miss* `(M, m)`; the Merkle
chain contains `M`'s decl; materialised members go through `C`'s refreshed interface. -/

example : reportL D Compiler.Policy.plain base edit3 {M} =
    some ⟨[Y], 2, true⟩ := by native_decide
example : reportL W Compiler.Policy.plain base edit3 {M} =
    some ⟨[C, Y], 3, true⟩ := by native_decide
example : reportL W walkPolicy base edit3 {M} =
    some ⟨[C, Y], 2, true⟩ := by native_decide
example : reportG false base edit3 {M} =
    some ⟨[Y], 2, true⟩ := by native_decide

end Zinc.Hier
