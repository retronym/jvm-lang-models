import Query.Lazy
import Query.Freeze
import Query.Interrupt
/-!
# True and spurious cycles, in the shapes scalac and dotc have

`Query.Lazy` says: if a program's definitions are well-founded (a ranked fixed point), lazy
forcing never black-holes, in any order. A compiler, though, does not force the program's
*semantic* facts one by one; it forces *its* facts, which bundle several semantic ones (a class's
whole info, every member's signature). Each witness below gives the same program three times:

* `fine`: one fact per thing the program defines, asking exactly what the definition needs. It
  has a ranked fixed point: the program is well-founded.
* the bundling a compiler uses, which black-holes: a **spurious** cycle, an artefact of the
  bundling, not of the program;
* where the other compiler bundles differently and does not.

A **true** cycle is one the fine rules already have: no bundling avoids it. Which rules are the
fine ones is the specification's choice, and `ir2` shows the specification and scalac disagreeing.

Each program was compiled with scalac 2.12.21 and 2.13.18 and dotc 3.9.0, and the verdicts are the
compilers' (`packages/scala/probes/forcing`).
-/

namespace ScalaTypes.Laziness

open Query Query.Lazy

/-- A rule that asks some facts and returns a string describing the answer. -/
def asks {Q : Type} : List Q → (List String → String) → Task Q (fun _ => String) String
  | [], f => .pure (f [])
  | q :: qs, f => .ask q fun v => asks qs fun vs => f (v :: vs)

/-! ## `fb5`: a class whose parent reads its own member

```scala
trait B[A <: B[A]]
class C extends B[C#T] { type T = C }
```

C's parent is `B[C#T]`; `C#T` is a member of `C` whose alias needs only `C`'s type constructor.
Well-founded. scalac 2.12.21 and 2.13.18: "illegal cyclic reference involving class C"; dotc
3.9.0 compiles it. -/

/-- The semantic facts: C's type constructor, its member scope (names only), the alias `T`, C's
parents, C's whole info. -/
inductive F5 | con | decls | aliasT | parents | info
  deriving DecidableEq, Repr

/-- Each asks what the definition needs: the parent reads `C#T`, which is found in the scope and
is an alias of `C` by name. -/
def fine5 : Rules F5 String
  | .con => asks [] fun _ => "C"
  | .decls => asks [] fun _ => "{T}"
  | .aliasT => asks [.con] fun vs => s!"= {vs}"
  | .parents => asks [.decls, .aliasT] fun vs => s!"B[{vs}]"
  | .info => asks [.parents, .decls] fun vs => s!"info {vs}"

def ρ5 : F5 → String := fun q => (fine5 q).run (fun q => match q with
  | .con => "C" | .decls => "{T}" | .aliasT => "= [C]" | .parents => "B[[{T}, = [C]]]"
  | .info => "info [B[[{T}, = [C]]], {T}]")

theorem fine5_ranked : Ranked fine5 ρ5 fun | .con => 0 | .decls => 0 | .aliasT => 1 | .parents => 2 | .info => 3 := by
  intro q q' h; cases q <;> simp [fine5, asks, Task.trace] at h <;> rcases h with rfl | rfl <;> decide

theorem fine5_fix : Fix fine5 ρ5 := by intro q; cases q <;> rfl

/-- scalac: parents and members are one fact, the class's info (`ClassInfoType`), completed by
one completer that types the parents first; looking up `C#T` needs C's info. -/
inductive S5 | con | info | aliasT
  deriving DecidableEq, Repr

def scalac5 : Rules S5 String
  | .con => asks [] fun _ => "C"
  | .aliasT => asks [.con] fun vs => s!"= {vs}"
  | .info => asks [.info, .aliasT] fun vs => s!"B[{vs}] + decls"

theorem scalac5_cycles : (force scalac5 10 [] (fun _ => none) .info).1 = .cyc .info := by decide

/-- dotc: the class completer first installs a `TempClassInfo` with the indexed members, then types
the parents, so `C#T` is found without C's final info. -/
inductive D5 | con | temp | aliasT | info
  deriving DecidableEq, Repr

def dotc5 : Rules D5 String
  | .con => asks [] fun _ => "C"
  | .temp => asks [] fun _ => "{T}"
  | .aliasT => asks [.con] fun vs => s!"= {vs}"
  | .info => asks [.temp, .aliasT] fun vs => s!"B[{vs}] + decls"

theorem dotc5_ok : (force dotc5 10 [] (fun _ => none) .info).1 = .ok "B[[{T}, = [C]]] + decls" := by
  decide

/-! ## A consumer of every member's signature

```scala
class A { def m: Int = 0; def n = /* asks about m */ }
```

`n` needs `m`'s signature only. Asking for `m` alone is fine; a consumer that asks for every
member's signature (overloading resolution, implicit search over a scope, `members.map(_.info)`)
includes `n` itself. The programmatic spike (scalac 2.13.18, `Spike.scala`) shows both: from inside
`n`'s completer, `A.info.member(m).info` is fine and `A.info.members.map(_.info)` is a cyclic
reference. -/

inductive Fm | m | n
  deriving DecidableEq, Repr

def fineM : Rules Fm String
  | .m => asks [] fun _ => "Int"
  | .n => asks [.m] fun vs => s!"from {vs}"

theorem fineM_ranked : Ranked fineM (fun q => (fineM q).run fun | .m => "Int" | .n => "from [Int]")
    fun | .m => 0 | .n => 1 := by
  intro q q' h; cases q <;> simp [fineM, asks, Task.trace] at h; subst h; decide

/-- The same, with `n` asking every member's signature. -/
def allSigsM : Rules Fm String
  | .m => asks [] fun _ => "Int"
  | .n => asks [.m, .n] fun vs => s!"from {vs}"

theorem fineM_ok : (force fineM 5 [] (fun _ => none) .n).1 = .ok "from [Int]" := by decide
theorem allSigsM_cycles : (force allSigsM 5 [] (fun _ => none) .n).1 = .cyc .n := by decide

/-! ## `ir2`: the specification decides

```scala
trait T { def m = new C().m }
class C extends T { override def m = 1 }
```

By the SLS, an inferred result type is the type of the right-hand side, so `C.m : Int` needs
nothing, `T.m` needs `C.m`: well-founded. scalac types an overriding method's right-hand side with
the overridden method's result type as the expected type, so `C.m` asks `T.m`; dotc (and scalac
under `-Xsource:3 infer-override`) takes `C.m`'s type from `T.m` outright. Under either rule the
cycle is true: no bundling avoids it. All three compilers reject the program. -/

inductive Fi | tm | cm
  deriving DecidableEq, Repr

/-- The SLS's rule. -/
def slsI : Rules Fi String
  | .cm => asks [] fun _ => "Int"
  | .tm => asks [.cm] fun vs => s!"{vs}"

/-- scalac's and dotc's rules: the overriding method reads the overridden one. -/
def implI : Rules Fi String
  | .cm => asks [.tm] fun vs => s!"Int (expected {vs})"
  | .tm => asks [.cm] fun vs => s!"{vs}"

theorem slsI_ranked : Ranked slsI (fun q => (slsI q).run fun | .cm => "Int" | .tm => "[Int]")
    fun | .cm => 0 | .tm => 1 := by
  intro q q' h; cases q <;> simp [slsI, asks, Task.trace] at h; subst h; decide

theorem implI_cycles : (force implI 5 [] (fun _ => none) .cm).1 = .cyc .cm := by decide

/-- Under the compilers' rules no ranking exists at all: `C.m` and `T.m` each ask the other. A
true cycle. -/
theorem implI_unranked (ρ : Fi → String) (r : Fi → Nat) : ¬ Ranked implI ρ r := by
  intro h
  have h1 := h .cm .tm (by simp [implI, asks, Task.trace])
  have h2 := h .tm .cm (by simp [implI, asks, Task.trace])
  omega

/-- scalac's bundling has no ranking either: its class info asks itself. Spurious, since the
fine rules are ranked (`fine5_ranked`). -/
theorem scalac5_unranked (ρ : S5 → String) (r : S5 → Nat) : ¬ Ranked scalac5 ρ r := by
  intro h
  have := h .info .info (by simp [scalac5, asks, Task.trace])
  omega

/-! ## Facts at a phase: versioned or overwritten

A symbol's name, owner, flags and info are asked *at a phase*. dotc keeps every version (a
denotation per period, `SingleDenotation.current`), so an answer at typer never changes. scalac
keeps a history only for the info (`TypeHistory`) and a phase mask for the flags; LambdaLift and
private-name expansion overwrite the name and owner, and UnCurry's info transformer sets `METHOD`
in the raw flags. So a typer-phase question asked again after those phases ran gets a later
phase's answer: the result depends on what was forced in between.

`packages/scala/probes/forcing/Phases2.scala` and `Phases3.scala` ask the same questions of a real
run: in scalac 2.12.21 and 2.13.18, three typer-phase answers change after the run (an expanded
private name, a local class's name and owner, a nested object's `isMethod`); in dotc 3.9.0, none.
The model is the two stores: -/

/-- A versioned fact: its values from a phase on, newest first (dotc's denotations, scalac's
`TypeHistory`). A read at phase `p` takes the newest version valid at `p`. -/
def readVersioned (h : List (Nat × String)) (p : Nat) : Option String :=
  (h.find? fun (q, _) => q ≤ p).map (·.2)

/-- An overwritten fact: one slot (scalac's `rawname`, `rawowner`, raw flags). A read ignores the
phase. -/
def readOverwritten (slot : String) (_p : Nat) : String := slot

/-- Phases as numbers: typer and lambdalift. -/
def typer : Nat := 4
def lambdalift : Nat := 30

/-- `class L` local to a method: its name before LambdaLift has run, and after. Versioned (dotc):
the typer-phase answer is the same both times. Overwritten (scalac): it changes. -/
theorem localName_versioned :
    readVersioned [(typer, "L")] typer = readVersioned [(lambdalift, "L$1"), (typer, "L")] typer := by
  decide

theorem localName_overwritten : readOverwritten "L" typer ≠ readOverwritten "L$1" typer := by decide

/-! ## An implicit candidate skipped while it is completed

```scala
// O.scala
object O {
  implicit val x: Int = 1
  implicit def y = U.z + 1
}
// U.scala
object U { import O._; def z = implicitly[Int] }
```

`y`'s type needs `U.z`'s, whose implicit search considers `x` and `y`. scalac skips a candidate
whose symbol is being completed, so the outcome depends on what is in progress:

* typing `O.scala` first: completing `y` types `U.z`, which skips `y` and resolves to `x`; the
  program compiles, and `U.z` is `1`;
* typing `U.scala` first: `U.z`'s search forces `y`, which needs `U.z`: "recursive method z needs
  result type";
* recompiling `U.scala` alone against the classfiles (what Zinc does after an edit to it): `y`'s
  type is read from the classfile, both candidates are eligible: "ambiguous implicit values".

So a clean build accepts what an incremental build rejects. Measured with scalac 2.12.21 and
2.13.18 (2.13 warns that an implicit definition should have an explicit type); dotc 3.9.0 rejects
both orders, since Scala 3 requires that type. The facts: `y`'s type and `U.z`'s resolution. -/

inductive Fz | y | z
  deriving DecidableEq, Repr

/-- `y` forces `z`; `z` peeks at `y` (implicit search skips a candidate in progress). -/
def implicitRules : PRules Fz String
  | .y => .ask (.force .z) fun _ => .pure "Int"
  | .z => .ask (.peek .y) fun ty =>
      .pure (if ty == "Int" then "ambiguous: x, y" else "x")

/-- Typing `O.scala` first: `z` resolves to `x`. -/
theorem implicitSkip_O_first :
    (forcePeekAll implicitRules "absent" 10 [.y, .z] (fun _ => none)).1 = [.ok "Int", .ok "x"] := by
  decide

/-- Typing `U.scala` first: a cyclic reference. -/
theorem implicitSkip_U_first :
    (forcePeekAll implicitRules "absent" 10 [.z, .y] (fun _ => none)).1.head? = some (.cyc .z) := by
  decide

/-- Recompiling `U.scala` alone, with `y`'s type from the classfile: ambiguous. -/
theorem implicitSkip_separate :
    (forcePeekAll implicitRules "absent" 10 [.z] (fun q => if q = .y then some "Int" else none)).1 =
      [.ok "ambiguous: x, y"] := by
  decide

/-- With the peek read as a force, the rules have a fixed point (`y : Int`, `z` ambiguous): the
answer of a build in which `y` is finished before `z` asks, which is the separate compilation. It
is not ranked (`y` asks `z`, `z` peeks `y`). -/
theorem implicitRules_fix :
    Query.Interrupt.PFix implicitRules fun | .y => "Int" | .z => "ambiguous: x, y" := by
  intro q; cases q <;> rfl

/-- **scalac memoizes the order-dependent answer**: typing `O.scala` first stores `z = x`, which
is not `z`'s value under the fixed point. A later consumer in the same run (another unit's
implicit search through `U.z`) inherits the typing order. -/
theorem implicitSkip_memoizes_wrong :
    (forcePeekAll implicitRules "absent" 10 [.y, .z] (fun _ => none)).2 .z = some "x" := by decide

/-- **Full taint rejects the program in every order**, as dotc does: `z`'s answer `x` is tainted
and not stored, nor is `y`'s, and the second demand of `z` forces `y`, which forces `z`: a cyclic
reference. The store never holds a value that is not the fixed point's
([`forceT_agree`](../../query/Query/Interrupt.lean)). -/
theorem implicitSkip_taint_rejects :
    (Query.Interrupt.forceTAll implicitRules false "absent" 10 [.y, .z] (fun _ => none)).1 =
      [.ok "Int", .cyc .z] ∧
    (Query.Interrupt.forceTAll implicitRules false "absent" 10 [.y, .z] (fun _ => none)).2 .z = none := by
  decide

/-- **IntelliJ's rule caches the re-entered `y`** (its value does not depend on `z`'s) and not the
tainted `z`, so the second demand of `z` finds `y` finished and answers as the separate
compilation does: ambiguous. Here the root of the cycle happens to be order-independent. -/
theorem implicitSkip_psi_ambiguous :
    (Query.Interrupt.forceTAll implicitRules true "absent" 10 [.y, .z] (fun _ => none)).1 =
      [.ok "Int", .ok "ambiguous: x, y"] := by
  decide

/-! ## A wildcard export reads a member set that is still growing (dotc)

```scala
// A.scala
object A { export B.*; def a = 1 }
// B.scala
object B { export A.a; def b = 2 }
```

`A`'s wildcard export reads `B`'s members (`membersBasedOnFlags`). `B`'s own export forwarders are
added to its declarations while `B` completes, so `B`'s member set is a fact that grows, read
without a freeze. dotc 3.9.0, typing `A.scala` first: `B` completes, gets its forwarder `a`, and
`A` exports it too, clashing with `A`'s `def a` ("Conflicting definitions"). Typing `B.scala`
first: `B` is mid-completion when `A` reads its members, sees only `b`, and the program compiles.
Recompiling `A.scala` alone against the classfiles fails again. The pushes are `B`'s members, `b`
when it is indexed and `a` when its export is processed; the read is `A`'s wildcard. -/

/-- `A` read `B`'s members after `B`'s export (A first) or before it (B first). -/
theorem exportOrder_reads_differ :
    Query.Freeze.unguarded [.push "b", .push "a", .read] [] ≠
      Query.Freeze.unguarded [.push "b", .read, .push "a"] [] := by
  decide

/-- A freeze would make the second order fail instead of compiling. -/
theorem exportOrder_guarded :
    Query.Freeze.guarded [.push "b", .read, .push "a"] [] false = none := by decide

end ScalaTypes.Laziness
