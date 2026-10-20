/-!
# Track LUB: the join of class types, as scalac 2.12/2.13 and dotc 3 compute it

A join over a class hierarchy, in the two shapes the compilers use, calibrated against
`packages/scala-types/probes/lub` (`results.txt`, scalac 2.12.21 and 2.13.18, dotc 3.9.0).

* **scalac** (`GlbLubs.lub`): drop the inputs below another input (`elimSub`), walk the inputs' base
  type sequences, which are sorted by `Symbol.isLess` (longer sequence first, then by symbol id), keep
  the classes common to all (`lubList`), then the minimal ones (`spanningTypes`). The parents of the
  result are in `isLess` order, so the join is a function of the *set* of inputs (`lubS_comm`) and of the
  ids, which follow creation order: declaration order in a joint compilation, file-name order from a
  classpath directory (`lubS_ids`). scala/scala#11291 breaks the tie by name instead (`lubS_byName`).
* **dotc** (`TypeComparer.lub`, `TypeOps.orDominator`, `ConstraintHandling.widenInferred`): an inferred
  join is first a union; widening it intersects the base classes in the *first* operand's linearization
  order and keeps the dominators, so the parents of the result follow the first operand
  (`joinD_order`), while their set does not (`joinD_comm`). If every dominator is transparent (`Product`,
  `Serializable`, `Object`, ...), the union is kept, which breaks associativity: fixing an inner join in a
  `val` changes the outer one to a type that is not equivalent (`widenD_not_assoc`). A kept union is
  erased by `erasedLub`, which prefers the *first* operand's order (`eraseUnion_order`); the cut
  scala/scala3#24148 proposes restores the preference for classes but not symmetry (`eraseUnion_fixed_order`),
  while erasing the join, as the specification says, is symmetric (`eraseJoin_symm`).

Types here are class references (with an optional alias name, for `elimSub`'s choice among equivalent
types); type arguments, refinements and depth truncation are future work (the probe's `fbound`,
`variance` and `refine` worlds). No Mathlib: witnesses by `decide`.
-/

namespace ScalaTypes.Lub

/-- A class or trait: its name, whether it is a trait, whether dotc treats it as transparent
(`Definitions.isAssumedTransparent`: `Any`, `Object`, `Product`, `Serializable`, ...) and its declared
parents, superclass first. -/
structure Cls where
  name : String
  isTrait : Bool := true
  transparent : Bool := false
  parents : List Nat := []
  deriving Repr

/-- A hierarchy; a class is its index. -/
abbrev Hier := List Cls

def cls (h : Hier) (c : Nat) : Cls := h.getD c {name := "?"}

/-- Scala linearization (SLS 5.1.2): `L(C) = C, L(Pn) +: … +: L(P1)`, where in `a +: b` the elements of
`b` replace their occurrences in `a`. -/
def linF (h : Hier) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, c => c :: (cls h c).parents.foldl (fun acc p => (linF h fuel p).filter (fun x => !acc.contains x) ++ acc) []

def lin (h : Hier) (c : Nat) : List Nat := linF h (h.length + 1) c

/-- `a` derives from `b`. -/
def derives (h : Hier) (a b : Nat) : Bool := (lin h a).contains b

/-! ## scalac -/

/-- A type in the scalac model: a class, possibly named through an alias (`type KK = K`). -/
structure Ty where
  c : Nat
  alias : Option String := none
  deriving DecidableEq, Repr

/-- How `Symbol.isLess` breaks a tie between base classes of the same depth: by symbol id (2.12.21,
2.13.18), from a table of ids, or by name (scala/scala#11291). -/
inductive Tie | id (ids : List Nat) | name

def btsLen (h : Hier) (c : Nat) : Nat := (lin h c).length

/-- `Symbol.isLess`: the longer base type sequence first, then the tie-break. -/
def isLess (h : Hier) : Tie → Nat → Nat → Bool
  | .id ids, a, b => btsLen h a > btsLen h b || (btsLen h a == btsLen h b && ids.getD a 0 < ids.getD b 0)
  | .name, a, b => btsLen h a > btsLen h b || (btsLen h a == btsLen h b && decide ((cls h a).name < (cls h b).name))

def insertBy (lt : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

def sortBy (lt : Nat → Nat → Bool) (xs : List Nat) : List Nat := xs.foldr (insertBy lt) []

/-- A base type sequence: the base classes in `isLess` order, that is, the one order of all classes restricted
to the base classes (for a total `isLess`, the same as sorting the linearization). -/
def bts (h : Hier) (t : Tie) (c : Nat) : List Nat :=
  (sortBy (isLess h t) (List.range h.length)).filter fun d => derives h c d

/-- `maxTypes`'s `stacked` with `po` = subtyping, as `elimSub` uses it for up to five types: of two
equivalent types the *first* survives. -/
def stackedF (h : Hier) : Nat → List Ty → List Ty
  | 0, _ => []
  | _, [] => []
  | n + 1, t :: ts =>
    let ts2 := stackedF h n (ts.filter fun u => !derives h u.c t.c)
    if ts2.any (fun u => derives h t.c u.c) then ts2 else t :: ts2

def stacked (h : Hier) (ts : List Ty) : List Ty := stackedF h (ts.length + 1) ts

/-- `spanningTypes`: keep the first, drop the later ones it derives from, repeat. -/
def spanningF (h : Hier) : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | fuel + 1, c :: rest => c :: spanningF h fuel (rest.filter fun d => !derives h c d)

/-- `lubList` for class types: the classes in every input's base type sequence, in `isLess` order.
(The frontier walk over sorted sequences yields their intersection in that order.) -/
def lubList (h : Hier) (t : Tie) (ts : List Ty) : List Nat :=
  match ts with
  | [] => []
  | u :: _ => (bts h t u.c).filter fun c => ts.all fun v => derives h v.c c

/-- scalac's join: `elimSub`, then the spanning types of `lubList`, as an intersection (its parents). -/
def lubS (h : Hier) (t : Tie) (ts : List Ty) : List Ty :=
  match stacked h ts with
  | [u] => [u]
  | ts' => (spanningF h (h.length + 1) (lubList h t ts')).map fun c => {c}

/-- scalac's erasure of an intersection (`intersectionDominator`): the first class parent, else the first. -/
def eraseS (h : Hier) (ps : List Ty) : Option Nat :=
  match ps.find? (fun p => !(cls h p.c).isTrait) with
  | some p => some p.c
  | none => ps.head?.map (·.c)

/-! ## dotc -/

/-- `orBaseClasses` of a union of classes: the first operand's base classes that every operand has. -/
def commonD (h : Hier) : List Nat → List Nat
  | [] => []
  | a :: rest => (lin h a).filter fun c => rest.all fun b => derives h b c

/-- `dominators`: the common base classes no other common base class derives from. dotc accumulates them by
prepending while walking the first operand's linearization, so they come out reversed. -/
def doms (h : Hier) (cs : List Nat) : List Nat :=
  (cs.filter fun c => !cs.any fun d => d != c && derives h d c).reverse

/-- `orDominator`: the join of a union, as an intersection (its parents). -/
def joinD (h : Hier) (u : List Nat) : List Nat := doms h (commonD h u)

/-- A type in the dotc model: a union of intersections of classes. -/
abbrev DTy := List (List Nat)

/-- The base classes of an intersection, and their common ones over a union, first operand's order. -/
def basesI (h : Hier) (cs : List Nat) : List Nat :=
  cs.foldl (fun acc c => acc ++ (lin h c).filter fun x => !acc.contains x) []

def joinU (h : Hier) : DTy → List Nat
  | [] => []
  | i :: rest => doms h ((basesI h i).filter fun c => rest.all fun j => (basesI h j).contains c)

/-- `widenInferred` for a union in a `val`'s type: the join, unless all of it is transparent, in which case
the union is kept; then `dropTransparentTraits`. -/
def widenD (h : Hier) (u : DTy) : DTy :=
  if u.length ≤ 1 then u
  else
    let j := joinU h u
    if j.all fun c => (cls h c).transparent then u
    else
      let k := j.filter fun c => !((cls h c).transparent && (cls h c).isTrait)
      [if k.isEmpty then j else k]

/-- A class `c` is in a type (an instance of `c` has it). -/
def inD (h : Hier) (c : Nat) (u : DTy) : Bool := u.any fun cs => cs.all fun d => derives h c d

/-- `takeUntil` in `TypeErasure.erasedLub`: `takeWhile` plus one. -/
def takeUntil (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => if p x then x :: takeUntil p xs else [x]

/-- `erasedLub` of two classes: the first operand's base classes that the second derives from, cut by
`takeUntil`, then the minimal ones, and the *last* of those. `upToClass` is the cut the comment and the
specification intend (every candidate up to the first class: `takeUntil (_.is(Trait))`); dotc 3.9.0 has
`takeUntil (!_.is(Trait))`, which stops at the first *trait* (scala/scala3#24148). -/
def eraseUnion (h : Hier) (upToClass : Bool) (a b : Nat) : Option Nat :=
  let common := (lin h a).filter fun c => derives h b c
  let cands := takeUntil (fun c => if upToClass then (cls h c).isTrait else !(cls h c).isTrait) common
  (cands.filter fun c => cands.all fun x => !derives h x c || x == c).getLast?

/-! ## Laws that hold -/

theorem derives_iff (h : Hier) (a b : Nat) : derives h a b = true ↔ b ∈ lin h a := by
  simp [derives]

theorem stacked_pair (h : Hier) (a b : Ty) (hab : derives h a.c b.c = false) (hba : derives h b.c a.c = false) :
    stacked h [a, b] = [a, b] := by
  simp [stacked, stackedF, hab, hba]

/-- scalac's join of two classes neither of which derives from the other does not depend on their order:
`elimSub` keeps both, and `lubList` keeps the classes both derive from, in the one `isLess` order. -/
theorem lubS_comm (h : Hier) (t : Tie) (a b : Ty) (hab : derives h a.c b.c = false) (hba : derives h b.c a.c = false) :
    lubS h t [a, b] = lubS h t [b, a] := by
  have s1 := stacked_pair h a b hab hba
  have s2 := stacked_pair h b a hba hab
  have l : lubList h t [a, b] = lubList h t [b, a] := by
    simp only [lubList, bts, List.all_cons, List.all_nil, Bool.and_true, List.filter_filter]
    congr 1; funext c; cases derives h a.c c <;> cases derives h b.c c <;> rfl
  simp only [lubS, s1, s2, l]

/-- Every class `spanningF` returns is one it was given. -/
theorem spanningF_sub (h : Hier) : ∀ (n : Nat) (l : List Nat) (x : Nat), x ∈ spanningF h n l → x ∈ l
  | 0, _, _, hx => by simp [spanningF] at hx
  | _ + 1, [], _, hx => by simp [spanningF] at hx
  | n + 1, c :: rest, x, hx => by
    simp only [spanningF, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mp (spanningF_sub h n _ x hx)).1

/-- scalac's join is an upper bound: when `elimSub` keeps both inputs, both derive from every parent of the
result. -/
theorem lubS_upper (h : Hier) (t : Tie) (a b : Ty) (hab : derives h a.c b.c = false) (hba : derives h b.c a.c = false)
    (p : Ty) (hp : p ∈ lubS h t [a, b]) : derives h a.c p.c = true ∧ derives h b.c p.c = true := by
  have s1 := stacked_pair h a b hab hba
  simp only [lubS, s1, List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  have := spanningF_sub h _ _ c hc
  simp only [lubList, List.all_cons, List.all_nil, Bool.and_true, List.mem_filter, Bool.and_eq_true] at this
  exact this.2

/-- dotc's dominators depend only on which classes are common, not on the order they are listed in. -/
theorem doms_mem (h : Hier) (cs ds : List Nat) (e : ∀ x, x ∈ cs ↔ x ∈ ds) (c : Nat) :
    c ∈ doms h cs ↔ c ∈ doms h ds := by
  have hany : (cs.any fun d => d != c && derives h d c) = (ds.any fun d => d != c && derives h d c) := by
    cases h1 : cs.any (fun d => d != c && derives h d c) <;> cases h2 : ds.any (fun d => d != c && derives h d c) <;> try rfl
    · obtain ⟨d, hd, hd'⟩ := List.any_eq_true.mp h2
      have := List.any_eq_false.mp h1 d ((e d).mpr hd); simp_all
    · obtain ⟨d, hd, hd'⟩ := List.any_eq_true.mp h1
      have := List.any_eq_false.mp h2 d ((e d).mp hd); simp_all
  simp only [doms, List.mem_reverse, List.mem_filter, e c, hany]

/-- dotc's join of two classes has the same parents in either order, as a set (`joinD_order`: not as a list). -/
theorem joinD_comm (h : Hier) (a b c : Nat) : c ∈ joinD h [a, b] ↔ c ∈ joinD h [b, a] := by
  apply doms_mem
  intro x
  simp only [commonD, List.all_cons, List.all_nil, Bool.and_true, List.mem_filter, ← derives_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- dotc's join is an upper bound: both operands derive from each of its parents. -/
theorem joinD_upper (h : Hier) (a b c : Nat) (hc : c ∈ joinD h [a, b]) : derives h a c = true ∧ derives h b c = true := by
  simp only [joinD, doms, commonD, List.mem_reverse, List.mem_filter, List.all_cons, List.all_nil, Bool.and_true] at hc
  exact ⟨(derives_iff h _ _).mpr hc.1.1, hc.1.2⟩

/-! ## The worlds, and what fails

Each hierarchy is a world of `probes/lub/worlds.py`; class 0 is `Object`. -/

/-- `traits`: `trait Zed; trait Abe; class S extends Zed with Abe; class T extends Abe with Zed`. -/
def traits : Hier := [
  {name := "Object", isTrait := false, transparent := true},
  {name := "Zed", parents := [0]}, {name := "Abe", parents := [0]},
  {name := "S", isTrait := false, parents := [0, 1, 2]}, {name := "T", isTrait := false, parents := [0, 2, 1]}]

/-- Symbol ids in a joint compilation follow declaration order; from a classpath directory, file-name order
(`Abe.class` before `S.class`, `T.class` and `Zed.class`). -/
def jointIds : List Nat := [0, 1, 2, 3, 4]
def separateIds : List Nat := [0, 4, 1, 2, 3]

/-- scalac: `if (b) new S else new T` is `Zed with Abe` (erased to `Zed`) when compiled with the traits and
`Abe with Zed` (erased to `Abe`) against their classfiles, as `results.txt` records for 2.12.21 and 2.13.18. -/
theorem lubS_ids :
    lubS traits (.id jointIds) [{c := 3}, {c := 4}] = [{c := 1}, {c := 2}] ∧
    lubS traits (.id separateIds) [{c := 3}, {c := 4}] = [{c := 2}, {c := 1}] ∧
    eraseS traits (lubS traits (.id jointIds) [{c := 3}, {c := 4}]) = some 1 ∧
    eraseS traits (lubS traits (.id separateIds) [{c := 3}, {c := 4}]) = some 2 := by decide

/-- scala/scala#11291: ordering ties by name, both compilation modes give `Abe with Zed`. -/
theorem lubS_byName : lubS traits .name [{c := 3}, {c := 4}] = [{c := 2}, {c := 1}] := by decide

/-- dotc: the parents follow the first operand's linearization (`Zed & Abe` for `if (b) s else t`, `Abe & Zed`
for `if (b) t else s`), in either compilation mode. -/
theorem joinD_order : joinD traits [3, 4] = [1, 2] ∧ joinD traits [4, 3] = [2, 1] := by decide

/-- `alias`: `trait K; object H { type KK = K }`. Of two equivalent types `elimSub` keeps the first, in both
compilers (dotc's `dropIfSub` likewise): `if (b) k else kk` is `K`, `if (b) kk else k` is `H.KK`. -/
def alias : Hier := [{name := "Object", isTrait := false}, {name := "K", parents := [0]}]

theorem lubS_alias :
    lubS alias .name [{c := 1}, {c := 1, alias := some "KK"}] = [{c := 1}] ∧
    lubS alias .name [{c := 1, alias := some "KK"}, {c := 1}] = [{c := 1, alias := some "KK"}] := by decide

/-- `cases`: `sealed trait Shape; case class Circle(r: Int) extends Shape`, `Square`, `case object Point`, and an
unrelated `case class Other(x: Int)`; `Product` and `Serializable` are transparent traits. -/
def cases : Hier := [
  {name := "Object", isTrait := false, transparent := true},
  {name := "Product", transparent := true, parents := [0]}, {name := "Serializable", transparent := true, parents := [0]},
  {name := "Shape", parents := [0]},
  {name := "Circle", isTrait := false, parents := [0, 3, 1, 2]}, {name := "Square", isTrait := false, parents := [0, 3, 1, 2]},
  {name := "Point", isTrait := false, parents := [0, 3, 1, 2]}, {name := "Other", isTrait := false, parents := [0, 1, 2]}]

/-- dotc: `val t = if (b) ci else sq` is `Shape` (the join, with the transparent traits dropped); joining it
with `ot` gives a join of `Object` only, transparent, so the union `Shape | Other` is kept. Joining the three
at once keeps `Circle | Square | Other`. The two are not equivalent: `Point` is in the first only. Extracting
a `val` changes the inferred type. -/
theorem widenD_not_assoc :
    widenD cases [[4], [5]] = [[3]] ∧
    widenD cases (widenD cases [[4], [5]] ++ [[7]]) = [[3], [7]] ∧
    widenD cases [[4], [5], [7]] = [[4], [5], [7]] ∧
    inD cases 6 [[3], [7]] = true ∧ inD cases 6 [[4], [5], [7]] = false := by decide

/-- scalac on the same world: `Product with Serializable with Shape`, the classic case-class join (there is no
union to keep, so no `val` changes it). -/
theorem lubS_cases :
    lubS cases (.id (List.range 8)) [{c := 4}, {c := 5}] = [{c := 1}, {c := 2}, {c := 3}] := by decide

/-- `transparent`: `abstract class L extends Product with Serializable`, `abstract class N extends Serializable
with Product`. The join is transparent, so dotc keeps `L | N`, and erases it by the first operand: `if (b) l
else n` erases to `java.io.Serializable`, `if (b) n else l` to `Product` (`results.txt`; a method overriding
one with the other order gets a bridge). -/
def transparentW : Hier := [
  {name := "java.lang.Object", isTrait := false, transparent := true},
  {name := "scala.Product", transparent := true, parents := [0]}, {name := "java.io.Serializable", transparent := true, parents := [0]},
  {name := "L", isTrait := false, parents := [0, 1, 2]}, {name := "N", isTrait := false, parents := [0, 2, 1]}]

theorem eraseUnion_order :
    widenD transparentW [[3], [4]] = [[3], [4]] ∧
    eraseUnion transparentW false 3 4 = some 2 ∧ eraseUnion transparentW false 4 3 = some 1 := by decide

/-- Removing the negation (scala/scala3#24148's proposal) restores the preference for classes, but not symmetry:
of two unrelated traits, "the last minimum in the first operand's linearization" still depends on the order. -/
theorem eraseUnion_fixed_order :
    eraseUnion transparentW true 3 4 = some 1 ∧ eraseUnion transparentW true 4 3 = some 2 := by decide

/-- The specification's erasure of a union is the erasure of its join; the erasure of an intersection is
`erasedGlb`, the minimum of a total order (classes before traits, then by full name), so it is symmetric. -/
def eraseJoin (h : Hier) (u : List Nat) : Option Nat :=
  let ds := joinD h u
  match ds.find? (fun c => !(cls h c).isTrait) with
  | some c => some c
  | none => ds.foldl (fun acc c => match acc with
      | none => some c
      | some m => if decide ((cls h c).name < (cls h m).name) then some c else some m) none

theorem eraseJoin_symm : eraseJoin transparentW [3, 4] = some 2 ∧ eraseJoin transparentW [4, 3] = some 2 := by decide

end ScalaTypes.Lub
