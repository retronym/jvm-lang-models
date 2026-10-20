/-!
# Track LUB with type arguments: variance, F-bounds and the depth limit

`ScalaTypes.Lub` joins class types without arguments. Here classes take type parameters, each with a variance
and an upper bound that may mention the parameters (`trait Fb[T <: Fb[T]]`), and a join must also merge the
arguments of each common base type:

* **scalac** (`Types.mergePrefixAndArgs`): equal arguments stay; otherwise a covariant argument is the join of
  the arguments and a contravariant one their meet, each at `depth - 1`; an invariant one is their join if that
  is below their meet, else a wildcard `_ >: meet <: join`. At depth zero, differing arguments give `NoType` and
  the base type is dropped from `lubList`, so the join falls back on the remaining common base classes:
  that is where `Object` comes from in `Fb[Fb[Object]]`. The depth starts at `lubDepth`, computed from the
  inputs' type and base type sequence depths. `glb` keeps its inputs' order.
* **dotc** (`TypeComparer.lubArgs`, `TypeOps.orDominator`): a covariant argument is the union of the arguments,
  a contravariant one their intersection, an invariant one a wildcard `? >: a & b <: a | b`. No depth: the union
  is the least upper bound.

Bounds checks (`wfS`, `wfD`) are as calibrated: scalac checks concrete arguments and accepts a wildcard;
dotc checks a wildcard's upper bound against the parameter's bound.

Calibrated against `probes/lub/results.txt`, worlds `fbound`, `fboundco` and `variance` (scalac 2.12.21,
2.13.18, dotc 3.9.0); each witness compares the model's printed type with the compiler's. Everything is
computed with fuel so that `decide` can evaluate it.
-/

namespace ScalaTypes.LubArgs

inductive Var | co | contra | inv
  deriving DecidableEq, Repr

/-- Types: `Any`, `Nothing`, a class's type parameter (in declarations), a class applied to arguments,
an intersection, a union (dotc), and a wildcard argument with its bounds. -/
inductive Ty where
  | any | nothing
  | param (i : Nat)
  | app (c : Nat) (args : List Ty)
  | and (ts : List Ty)
  | or (ts : List Ty)
  | wild (lo hi : Ty)
  deriving Repr, Inhabited

/-- Structural equality with fuel (a derived `BEq` on a nested inductive does not reduce in the kernel). -/
def Ty.eqF : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, a, b => match a, b with
    | .any, .any | .nothing, .nothing => true
    | .param i, .param j => i == j
    | .app c as, .app d bs => c == d && as.length == bs.length && (as.zip bs).all fun (x, y) => Ty.eqF n x y
    | .and as, .and bs | .or as, .or bs => as.length == bs.length && (as.zip bs).all fun (x, y) => Ty.eqF n x y
    | .wild l h, .wild l' h' => Ty.eqF n l l' && Ty.eqF n h h'
    | _, _ => false

instance : BEq Ty := ⟨Ty.eqF 40⟩

/-- A class: its name, kind, whether its instances are value types (boxed to `Object` in a generic
signature), whether dotc treats it as transparent, its type parameters (variance and upper bound, over
`param i`) and its parents (over `param i`), superclass first. -/
structure Cls where
  name : String
  isTrait : Bool := false
  isValue : Bool := false
  transparent : Bool := false
  tparams : List (Var × Ty) := []
  parents : List Ty := []

abbrev Hier := List Cls

def cls (h : Hier) (c : Nat) : Cls := h.getD c {name := "?"}

/-- Fuel for every recursion; the worlds are small. -/
def F : Nat := 40

def subst (as : List Ty) : Nat → Ty → Ty
  | 0, t => t
  | n + 1, t => match t with
    | .param i => as.getD i .any
    | .app c bs => .app c (bs.map (subst as n))
    | .and ts => .and (ts.map (subst as n))
    | .or ts => .or (ts.map (subst as n))
    | .wild lo hi => .wild (subst as n lo) (subst as n hi)
    | t => t

def parentsOf (h : Hier) : Ty → List Ty
  | .app c as => (cls h c).parents.map (subst as F)
  | _ => []

def head : Ty → Option Nat
  | .app c _ => some c
  | _ => none

/-- The base type of `t` for class `d`, if `t` derives from `d`. -/
def baseType (h : Hier) : Nat → Ty → Nat → Option Ty
  | 0, _, _ => none
  | n + 1, t, d => match t with
    | .app c _ => if c == d then some t else (parentsOf h t).findSome? (baseType h n · d)
    | _ => none

/-- Linearization of a class, over the heads of its parents (SLS 5.1.2). -/
def lin (h : Hier) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, c => c :: ((cls h c).parents.filterMap head).foldl (fun acc p => (lin h n p).filter (fun x => !acc.contains x) ++ acc) []

def vars (h : Hier) (c : Nat) : List Var := (cls h c).tparams.map (·.1)

/-- Subtyping, variance-aware; a wildcard on the left is read as its upper bound, on the right as its lower one
(outside argument position, where it is checked by its bounds). -/
def sub (h : Hier) : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, s, t => match s, t with
    | _, .any => true
    | .nothing, _ => true
    | .or ss, t => ss.all (sub h n · t)
    | s, .and ts => ts.all (sub h n s ·)
    | .and ss, t => ss.any (sub h n · t)
    | s, .or ts => ts.any (sub h n s ·)
    | .wild _ hi, t => sub h n hi t
    | s, .wild lo _ => sub h n s lo
    | .app _ _, .app d bs => match baseType h F s d with
      | some (.app _ as) => ((vars h d).zip (as.zip bs)).all fun (v, a, b) => match b with
        | .wild lo hi => match a with
          | .wild alo ahi => sub h n lo alo && sub h n ahi hi
          | a => sub h n lo a && sub h n a hi
        | b => match v with
          | .co => sub h n a b
          | .contra => sub h n b a
          | .inv => sub h n a b && sub h n b a
      | _ => false
    | _, _ => false

def s (h : Hier) := sub h F

/-! ## scalac -/

/-- `maxTypes`'s `stacked` with partial order `po`: of two related types, keep the one `po` says is higher;
of two equivalent ones, the first. -/
def stacked (po : Ty → Ty → Bool) : Nat → List Ty → List Ty
  | 0, _ => []
  | _, [] => []
  | n + 1, t :: ts =>
    let ts2 := stacked po n (ts.filter fun u => !po u t)
    if ts2.any (fun u => po t u) then ts2 else t :: ts2

def elimSub (h : Hier) (ts : List Ty) : List Ty := stacked (s h) (ts.length + 1) ts
def elimSuper (h : Hier) (ts : List Ty) : List Ty := stacked (fun a b => s h b a) (ts.length + 1) ts

def flattenAnd : List Ty → List Ty
  | [] => []
  | .and xs :: ts => xs ++ flattenAnd ts
  | t :: ts => t :: flattenAnd ts

/-- Order types by their class's base type sequence length, then by name: the canonical order the fix uses
for the parents of both `lub` and `glb` (scala/scala#11291 does this for `lub`'s ties). -/
def keyLt (h : Hier) (a b : Ty) : Bool :=
  match head a, head b with
  | some x, some y =>
    let lx := (lin h F x).length
    let ly := (lin h F y).length
    lx > ly || (lx == ly && decide ((cls h x).name < (cls h y).name))
  | _, _ => false

def insertTy (lt : Ty → Ty → Bool) (x : Ty) : List Ty → List Ty
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertTy lt x ys

/-- `glb`: drop supertypes of another input and intersect, in input order (scalac 2.12.21, 2.13.18), or in the
canonical order (`fix`). -/
def glbS (h : Hier) (fix : Bool := false) (ts : List Ty) : Ty :=
  let us := elimSuper h (flattenAnd ts)
  let us := if fix then us.foldr (insertTy (keyLt h)) [] else us
  match us with
  | [] => .any
  | [t] => t
  | us => .and us

def typeDepth : Nat → Ty → Nat
  | 0, _ => 0
  | n + 1, t => match t with
    | .app _ as => 1 + (as.map (typeDepth n)).foldl max 0
    | .and ts | .or ts => (ts.map (typeDepth n)).foldl max 0
    | .wild lo hi => max (typeDepth n lo) (typeDepth n hi)
    | _ => 1

def baseTypes (h : Hier) (t : Ty) : List Ty :=
  match head t with
  | some c => (lin h F c).filterMap (baseType h F t)
  | none => []

/-- `lubDepth`: the inputs' type depth and base type sequence depth, adjusted (`lubDepthAdjust`). -/
def lubDepth (h : Hier) (ts : List Ty) : Int :=
  let td := (ts.map (typeDepth F)).foldl max 0
  let bd := max td ((ts.map fun t => ((baseTypes h t).map (typeDepth F)).foldl max 0).foldl max 0)
  if bd ≤ 3 then bd else if bd ≤ 5 then max td (bd - 1) else if bd ≤ 7 then max td (bd - 2) else max (td - 1) (bd - 3)

def btsLen (h : Hier) (c : Nat) : Nat := (lin h F c).length

/-- `Symbol.isLess`, ties by id (declaration order). -/
def isLess (h : Hier) (a b : Nat) : Bool := btsLen h a > btsLen h b || (btsLen h a == btsLen h b && a < b)

def insertBy (lt : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

def dedupF : Nat → List Ty → List Ty
  | 0, _ => []
  | _, [] => []
  | n + 1, t :: ts => t :: dedupF n (ts.filter fun u => !(u == t))

def dedup (ts : List Ty) : List Ty := dedupF (ts.length + 1) ts

def derivesC (h : Hier) (a b : Nat) : Bool := (lin h F a).contains b

/-- `spanningTypes`: keep the first, drop later ones whose class it derives from, repeat. -/
def spanning (h : Hier) : Nat → List (Nat × Ty) → List Ty
  | 0, _ => []
  | _, [] => []
  | n + 1, (c, t) :: rest => t :: spanning h n (rest.filter fun (d, _) => !derivesC h c d)

/-- scalac's `lub` at a depth, with `mergePrefixAndArgs` for the base types of each common class (`none` is
`NoType`, and drops that base type). -/
def lubS (h : Hier) (fix : Bool) : Nat → Int → List Ty → Ty
  | 0, _, _ => .any
  | n + 1, d, ts =>
    let merge (c : Nat) (bts : List Ty) : Option Ty :=
      let argss := bts.map fun | .app _ as => as | _ => []
      let args := (vars h c).zipIdx.map fun (v, j) =>
        match dedup (argss.map (·.getD j .any)) with
        | [a] => some a
        | as =>
          if d == 0 then none
          else match v with
            | .co => some (lubS h fix n (d - 1) as)
            | .contra => some (glbS h fix as)
            | .inv =>
              let l := lubS h fix n (d - 1) as
              let g := glbS h fix as
              some (if s h l g then l else .wild g l)
      let as := args.filterMap id
      -- the fix: a merged argument that violates its parameter's bound becomes a wildcard below it, as scalac
      -- already does for an invariant parameter whose join is not below its meet
      let as := if fix then ((cls h c).tparams.zip as).map (fun ((_, b), a) => match a with
          | .wild _ _ => a
          | a => if s h a (subst as F b) then a else .wild .nothing a) else as
      if args.all Option.isSome then some (.app c as) else none
    match elimSub h ts with
    | [] => .nothing
    | [t] => t
    | us =>
      if d < 0 then .any
      else
        let cands := ((List.range h.length).foldr (insertBy (isLess h)) []).filter fun c =>
          us.all fun t => (baseType h F t c).isSome
        let merged := cands.filterMap fun c => (merge c (us.filterMap fun t => baseType h F t c)).map (c, ·)
        match spanning h F merged with
        | [] => .any
        | [p] => p
        | ps => .and ps

def lub (h : Hier) (ts : List Ty) : Ty := lubS h false F (lubDepth h ts) ts

/-- The fix: canonical order in `lub` and `glb`, and a bound-respecting cut. -/
def lubFix (h : Hier) (ts : List Ty) : Ty := lubS h true F (lubDepth h ts) ts

/-- scalac's bounds check as calibrated: every concrete argument conforms to its parameter's bound (with the
class's arguments substituted); a wildcard argument is accepted. -/
def wfS (h : Hier) : Nat → Ty → Bool
  | 0, _ => true
  | n + 1, t => match t with
    | .app c as => ((cls h c).tparams.zip as).all (fun ((_, b), a) => match a with
        | .wild _ _ => true
        | a => s h a (subst as F b)) && as.all (wfS h n)
    | .and ts | .or ts => ts.all (wfS h n)
    | .wild lo hi => wfS h n lo && wfS h n hi
    | _ => true

/-! ## dotc -/

def flattenOr : List Ty → List Ty
  | [] => []
  | .or xs :: ts => xs ++ flattenOr ts
  | t :: ts => t :: flattenOr ts

/-- `lub` of two types: one, if it is above the other; else the union. -/
def lubD (h : Hier) (a b : Ty) : Ty :=
  if s h b a then a else if s h a b then b else .or (flattenOr [a, b])

def glbD (h : Hier) (a b : Ty) : Ty :=
  if s h a b then a else if s h b a then b else .and (flattenAnd [a, b])

/-- `lubArgs`. -/
def lubArgs (h : Hier) (vs : List Var) (as bs : List Ty) : List Ty :=
  (vs.zip (as.zip bs)).map fun (v, a, b) =>
    if a == b then a
    else match v with
      | .co => lubD h a b
      | .contra => glbD h a b
      | .inv => .wild (glbD h a b) (lubD h a b)

/-- `orDominator` of `a | b`: the common base classes in `a`'s linearization, the dominators (accumulated by
prepending), each as the base type with merged arguments. -/
def joinD (h : Hier) (a b : Ty) : Ty :=
  match head a, head b with
  | some ca, some _ =>
    let common := (lin h F ca).filter fun c => (baseType h F b c).isSome
    let doms := (common.filter fun c => !common.any fun e => e != c && derivesC h e c).reverse
    let parts := doms.filterMap fun c => match baseType h F a c, baseType h F b c with
      | some (.app _ as), some (.app _ bs) => some (.app c (lubArgs h (vars h c) as bs))
      | _, _ => none
    match parts with
    | [] => .any
    | [p] => p
    | ps => .and ps
  | _, _ => .any

/-- The inferred type of `if (c) a else b` in a `val`: the union, widened to its join unless the join is
transparent. -/
def inferD (h : Hier) (a b : Ty) : Ty :=
  match lubD h a b with
  | .or _ =>
    let j := joinD h a b
    let parts := match j with | .and ps => ps | p => [p]
    if parts.all (fun p => match head p with | some c => (cls h c).transparent | none => true) then lubD h a b else j
  | t => t

/-- dotc's bounds check as calibrated: a concrete argument conforms to the bound; a wildcard's upper bound
conforms to the bound with the wildcard replaced by that upper bound. -/
def wfD (h : Hier) : Nat → Ty → Bool
  | 0, _ => true
  | n + 1, t => match t with
    | .app c as =>
      let as' := as.map fun | .wild _ hi => hi | a => a
      ((cls h c).tparams.zip as).all (fun ((_, b), a) => match a with
        | .wild _ hi => s h hi (subst as' F b)
        | a => s h a (subst as F b)) && as.all (wfD h n)
    | .and ts | .or ts => ts.all (wfD h n)
    | .wild lo hi => wfD h n lo && wfD h n hi
    | _ => true

/-! ## Printing, as the compilers print -/

def joinStr (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinStr sep xs

/-- scalac's (`dotc := false`) or dotc's printing. -/
def pr (h : Hier) (dotc : Bool) : Nat → Ty → String
  | 0, _ => "…"
  | n + 1, t => match t with
    | .any => "Any"
    | .nothing => "Nothing"
    | .param i => s!"T{i}"
    | .app c [] => (cls h c).name
    | .app c as => (cls h c).name ++ "[" ++ joinStr ", " (as.map (pr h dotc n)) ++ "]"
    | .and ts => joinStr (if dotc then " & " else " with ") (ts.map (pr h dotc n))
    | .or ts => joinStr " | " (ts.map (pr h dotc n))
    | .wild lo hi =>
      (if dotc then "?" else "_") ++ (if lo == .nothing then "" else " >: " ++ pr h dotc n lo) ++
        (if hi == .any then "" else " <: " ++ pr h dotc n hi)

/-- The class a Java generic signature uses for a type argument's bound: the first class parent of an
intersection, else its first parent; a value class boxes to `Object`. -/
def sigClass (h : Hier) (t : Ty) : String :=
  let ps := match t with | .and ps => ps | p => [p]
  match (ps.find? fun p => match head p with | some c => !(cls h c).isTrait | none => false) <|> ps.head? with
  | some p => match head p with
    | some c => if (cls h c).isValue then "Object" else (cls h c).name
    | none => "Object"
  | none => "Object"

/-! ## The world

`variance` and `fbound`/`fboundco` of `probes/lub/worlds.py`, in one hierarchy. -/

def w : Hier := [
  /- 0 -/ {name := "Object"},
  /- 1 -/ {name := "AnyVal"},
  /- 2 -/ {name := "Int", isValue := true, parents := [.app 1 []]},
  /- 3 -/ {name := "String", parents := [.app 0 []]},
  /- 4 -/ {name := "Inv", tparams := [(.inv, .any)], parents := [.app 0 []]},
  /- 5 -/ {name := "Co", tparams := [(.co, .any)], parents := [.app 0 []]},
  /- 6 -/ {name := "Contra", tparams := [(.contra, .any)], parents := [.app 0 []]},
  /- 7 -/ {name := "Fb", isTrait := true, tparams := [(.inv, .app 7 [.param 0])], parents := [.app 0 []]},
  /- 8 -/ {name := "Fa", parents := [.app 0 [], .app 7 [.app 8 []]]},
  /- 9 -/ {name := "Fc", parents := [.app 0 [], .app 7 [.app 9 []]]},
  /- 10 -/ {name := "Gb", isTrait := true, tparams := [(.co, .app 10 [.param 0])], parents := [.app 0 []]},
  /- 11 -/ {name := "Ga", parents := [.app 0 [], .app 10 [.app 11 []]]},
  /- 12 -/ {name := "Gc", parents := [.app 0 [], .app 10 [.app 12 []]]}]

def int : Ty := .app 2 []
def str : Ty := .app 3 []
def fa : Ty := .app 8 []
def fc : Ty := .app 9 []
def ga : Ty := .app 11 []
def gc : Ty := .app 12 []

def sS (t : Ty) := pr w false F t
def sD (t : Ty) := pr w true F t

/-! ## LUB3 and LUB6: each compiler rejects a join the other accepts -/

/-- Covariant F-bound (`trait Gb[+T <: Gb[T]]`): scalac's depth is 2, the merge gives up at depth zero and
falls back on `Object`, and the result violates the bound. dotc's `Gb[Ga | Gc]` conforms. -/
theorem lub3_covariant :
    lubDepth w [ga, gc] = 2 ∧
    sS (lub w [ga, gc]) = "Gb[Gb[Object]]" ∧ wfS w F (lub w [ga, gc]) = false ∧
    sD (inferD w ga gc) = "Gb[Ga | Gc]" ∧ wfD w F (inferD w ga gc) = true := by decide

/-- Invariant F-bound (`trait Fb[T <: Fb[T]]`): scalac's wildcard is accepted; dotc's
`Fb[? >: Fa & Fc <: Fa | Fc]` fails its bound (scala/scala3#9941). -/
theorem lub6_invariant :
    sS (lub w [fa, fc]) = "Fb[_ >: Fa with Fc <: Fb[_ >: Fa with Fc <: Object]]" ∧ wfS w F (lub w [fa, fc]) = true ∧
    sD (inferD w fa fc) = "Fb[? >: Fa & Fc <: Fa | Fc]" ∧ wfD w F (inferD w fa fc) = false := by decide

/-! ## LUB2: the order of a glb inside a lub -/

/-- `if (c) inv1 else inv2` and swapped: scalac's lower bound follows the branch order, and so does the class
the generic signature uses for it (`Inv<-Object>`, `Inv<-String>`, as `results.txt` records). -/
theorem lub2_glb_order :
    sS (lub w [.app 4 [int], .app 4 [str]]) = "Inv[_ >: Int with String]" ∧
    sS (lub w [.app 4 [str], .app 4 [int]]) = "Inv[_ >: String with Int]" ∧
    sigClass w (glbS w false [int, str]) = "Object" ∧ sigClass w (glbS w false [str, int]) = "String" := by decide

/-- The other variances, both compilers. -/
theorem variance_joins :
    sS (lub w [.app 5 [int], .app 5 [str]]) = "Co[Any]" ∧
    sS (lub w [.app 6 [int], .app 6 [str]]) = "Contra[Int with String]" ∧
    sD (inferD w (.app 5 [int]) (.app 5 [str])) = "Co[Int | String]" ∧
    sD (inferD w (.app 4 [int]) (.app 4 [str])) = "Inv[? >: Int & String <: Int | String]" := by decide

/-! ## Both joins are upper bounds, on this world -/

def pairs : List (Ty × Ty) :=
  [(fa, fc), (fc, fa), (ga, gc), (gc, ga), (.app 4 [int], .app 4 [str]), (.app 5 [int], .app 5 [str]),
   (.app 6 [int], .app 6 [str]), (fa, ga), (.app 4 [int], fa)]

theorem upper_bounds :
    pairs.all (fun (a, b) => s w a (lub w [a, b]) && s w b (lub w [a, b]) &&
      s w a (inferD w a b) && s w b (inferD w a b)) = true := by decide

/-! ## A systematic fix for scalac, checked on this world

Two changes: one canonical order for the parents of `lub` *and* `glb` (base type sequence length, then name),
and a merged argument that violates its parameter's bound becomes a wildcard bounded above by it
(`mergePrefixAndArgs` already does this for an invariant parameter when the join is not below the meet). -/

/-- LUB3 fixed: the covariant F-bounded join is well-formed. -/
theorem fix_lub3 :
    sS (lubFix w [ga, gc]) = "Gb[_ <: Gb[_ <: Object]]" ∧ wfS w F (lubFix w [ga, gc]) = true := by decide

/-- LUB2 fixed: the branch order no longer reaches the type or the generic signature. -/
theorem fix_lub2 :
    sS (lubFix w [.app 4 [int], .app 4 [str]]) = "Inv[_ >: Int with String]" ∧
    sS (lubFix w [.app 4 [str], .app 4 [int]]) = "Inv[_ >: Int with String]" := by decide

/-- On every pair of the world, the fixed join is well-formed, an upper bound of both inputs, and the same in
either order; the unfixed one is not (LUB2, LUB3). -/
theorem fix_laws :
    pairs.all (fun (a, b) => wfS w F (lubFix w [a, b]) && s w a (lubFix w [a, b]) && s w b (lubFix w [a, b]) &&
      lubFix w [a, b] == lubFix w [b, a]) = true ∧
    !(pairs.all (fun (a, b) => wfS w F (lub w [a, b]) && lub w [a, b] == lub w [b, a])) = true := by decide

end ScalaTypes.LubArgs
