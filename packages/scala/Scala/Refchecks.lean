import Scala.Lower
import ScalaTypes.Members
import Scala.RefchecksData
/-!
# Refchecks accepted, so no `AbstractMethodError` (Question 1)

A static promise kept by the dynamic semantics, across three layers. If `Members` (refchecks and
typer's inheritance checks) accepts a program of the 4,704-hierarchy space `Members.membersSpace` under
a dialect, and selects owner `O` for `m` in a concrete class `C`, then:

* **on HotSpot** (`Data`, the oracle: `members.py` compiled each program with scalac 2.12.21, 2.13.18
  or dotc 3.9.0 and ran `new C().m`), `O`'s `m` ran, except for the four programs of
  [scala/bug#13199](https://github.com/scala/bug/issues/13199) under Scala 2, which throw
  `AbstractMethodError` (`bug13199`);
* **in the model**, lowering the program with `Scala.lowerProgram` and linking `new C().m` with `Jvm`
  (constructor and `$init$` bodies run) enters `O`'s lowered method last (directly, or through `C`'s
  mixin forwarder and `O.m$`), or, for a trait's `val`, the class's accessor of it; so it links, and in
  particular throws no `AbstractMethodError`. Except for the rows `Scala.Lower` does not model
  (`lowerGap`): a class overriding a trait's `val` (the class's trait setter is missing) and a trait's
  `lazy val`.

And `Members` accepts exactly the programs the compiler accepts. Decided by the kernel in chunks of 400
programs (`all_of_chunks`); about 20 minutes, so the module is built on demand:
`lake build Scala.Refchecks`. Enumeration as testing, per `docs/specification.md`.
-/

namespace Scala.Refchecks

open Scala

/-- The 4,704 programs, each with its description and its index. -/
def space : List ((String × Program) × Nat) := Members.membersSpace.zipIdx

def accepts (dl : Dialect) (p : Program) : Bool :=
  match Members.reported dl p with | .ok es => es.isEmpty | .error _ => false

/-- `new C().m` against the lowered program and the prelude, constructors running. -/
def call (dl : Dialect) (p : Program) (c : String) : Except String (Except Jvm.LinkError (List String)) := do
  let cs ← lowerProgram dl p
  let pre ← preludeClasses dl
  pure (Jvm.outcome (toWorld (cs ++ pre))
    { sites := [.invokevirtual c "m" "()Ljava/lang/String;" c], init := some (ctorName, "()V") })

/-- `o` is a trait whose `m` is a concrete strict `val`: the class mixing it in implements the accessor. -/
def traitVal (p : Program) (o : String) : Bool :=
  p.any fun s => s.name == o && s.cls.any fun d =>
    d.kind == .trt && d.members.any fun m => m.name == "m" && m.isVal && !m.lzy && !m.abs

/-- The run links and ends in `o`'s lowered method, or is a class's accessor of `o`'s `val`. -/
def runsOwner (p : Program) (o : String) : Except String (Except Jvm.LinkError (List String)) → Bool
  | .ok (.ok l) => l.getLast? == some o || (traitVal p o && l.length == 1)
  | _ => false

/-- The rows `Scala.Lower` does not model: a trait's `lazy val`, and a trait's `val` that the class
overrides (scalac and dotc give the class the trait's setter, `T$_setter_$m_$eq`; lowering does not).

Spec: unspecified SLS §5.3.3: the encoding of a trait's `val` that a class overrides (the class
still implements the trait's setter, which `$init$` calls) and of a trait's `lazy val` in a class.
scalac 2.12.21, 2.13.18 and dotc 3.9.0 emit the setter (`javap`); `Scala.Lower` models neither
shape, so `Refchecks.refchecks_sound` leaves them out of the model's side. -/
def lowerGap (desc : String) : Bool :=
  desc.startsWith "T=lazy" || (desc.startsWith "T=val" && desc.endsWith "C=ovrVal")

/-- [scala/bug#13199](https://github.com/scala/bug/issues/13199): a class's abstract `def m`
re-abstracts a trait's `val m`, the subclass overrides it with a `val`, and Scala 2 drops the trait
setter that the trait's `$init$` calls.

Spec: contradicts SLS §5.1.4 / scalac 2.12.21, 2.13.18: refchecks accepts the program, as the
specification allows, but `new C().m` throws `AbstractMethodError`, since the trait setter that
`T.$init$` calls is dropped ([scala/bug#13199](https://github.com/scala/bug/issues/13199);
`Refchecks.bug13199_witnesses`). dotc rejects the class. -/
def bug13199 : List Nat := [3156, 3268, 3380, 3604]

def compiled : Dialect → List Nat
  | .s212 => Scala.Refchecks.Data.accepted_s212 | .s213 => Scala.Refchecks.Data.accepted_s213 | .s3 => Scala.Refchecks.Data.accepted_s3

def ran : Dialect → List (Nat × List (String × String))
  | .s212 => Scala.Refchecks.Data.ran_s212 | .s213 => Scala.Refchecks.Data.ran_s213 | .s3 => Scala.Refchecks.Data.ran_s3

/-- What HotSpot ran for `new c().m` in program `i`: an owner, or an exception (`!…`). -/
def ranAt (dl : Dialect) (i : Nat) (c : String) : Option String :=
  ((ran dl).lookup i).bind (·.lookup c)

/-- The three properties, for one program. -/
def holds (dl : Dialect) (x : (String × Program) × Nat) : Bool :=
  let ((desc, p), i) := x
  (accepts dl p == (compiled dl).contains i) &&
  (!accepts dl p || (dl != .s3 && bug13199.contains i) ||
    (Members.runs p).all fun (c, o) => ranAt dl i c == some o) &&
  (!accepts dl p || lowerGap desc || (Members.runs p).all fun (c, o) => runsOwner p o (call dl p c))

/-- A list's `all` from its chunks of `n`. -/
theorem all_of_chunks {α : Type} (p : α → Bool) (n : Nat) :
    ∀ (K : Nat) (l : List α), l.length ≤ K * n →
      (∀ k < K, ((l.drop (k * n)).take n).all p = true) → l.all p = true
  | 0, l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; rfl
  | K + 1, l, hl, h => by
    rw [← List.take_append_drop n l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks p n K (l.drop n) ?_ fun k hk => ?_⟩
    · simp only [List.length_drop]; rw [Nat.succ_mul] at hl; omega
    · have := h (k + 1) (by omega)
      rwa [List.drop_drop, show n + k * n = (k + 1) * n by rw [Nat.succ_mul]; omega]

theorem space_length : space.length ≤ 12 * 400 := by decide +kernel

set_option maxRecDepth 100000 in
theorem s212_0 : ((space.drop (0 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_1 : ((space.drop (1 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_2 : ((space.drop (2 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_3 : ((space.drop (3 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_4 : ((space.drop (4 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_5 : ((space.drop (5 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_6 : ((space.drop (6 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_7 : ((space.drop (7 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_8 : ((space.drop (8 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_9 : ((space.drop (9 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_10 : ((space.drop (10 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s212_11 : ((space.drop (11 * 400)).take 400).all (holds .s212) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s213_0 : ((space.drop (0 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_1 : ((space.drop (1 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_2 : ((space.drop (2 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_3 : ((space.drop (3 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_4 : ((space.drop (4 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_5 : ((space.drop (5 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_6 : ((space.drop (6 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_7 : ((space.drop (7 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_8 : ((space.drop (8 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_9 : ((space.drop (9 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_10 : ((space.drop (10 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s213_11 : ((space.drop (11 * 400)).take 400).all (holds .s213) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s3_0 : ((space.drop (0 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_1 : ((space.drop (1 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_2 : ((space.drop (2 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_3 : ((space.drop (3 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_4 : ((space.drop (4 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_5 : ((space.drop (5 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_6 : ((space.drop (6 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_7 : ((space.drop (7 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_8 : ((space.drop (8 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_9 : ((space.drop (9 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_10 : ((space.drop (10 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem s3_11 : ((space.drop (11 * 400)).take 400).all (holds .s3) = true := by
  decide +kernel

theorem holds_s212 : space.all (holds .s212) = true :=
  all_of_chunks _ 400 12 space space_length fun k hk =>
    match k, hk with
    | 0, _ => s212_0
    | 1, _ => s212_1
    | 2, _ => s212_2
    | 3, _ => s212_3
    | 4, _ => s212_4
    | 5, _ => s212_5
    | 6, _ => s212_6
    | 7, _ => s212_7
    | 8, _ => s212_8
    | 9, _ => s212_9
    | 10, _ => s212_10
    | 11, _ => s212_11
    | _ + 12, h => absurd h (by omega)

theorem holds_s213 : space.all (holds .s213) = true :=
  all_of_chunks _ 400 12 space space_length fun k hk =>
    match k, hk with
    | 0, _ => s213_0
    | 1, _ => s213_1
    | 2, _ => s213_2
    | 3, _ => s213_3
    | 4, _ => s213_4
    | 5, _ => s213_5
    | 6, _ => s213_6
    | 7, _ => s213_7
    | 8, _ => s213_8
    | 9, _ => s213_9
    | 10, _ => s213_10
    | 11, _ => s213_11
    | _ + 12, h => absurd h (by omega)

theorem holds_s3 : space.all (holds .s3) = true :=
  all_of_chunks _ 400 12 space space_length fun k hk =>
    match k, hk with
    | 0, _ => s3_0
    | 1, _ => s3_1
    | 2, _ => s3_2
    | 3, _ => s3_3
    | 4, _ => s3_4
    | 5, _ => s3_5
    | 6, _ => s3_6
    | 7, _ => s3_7
    | 8, _ => s3_8
    | 9, _ => s3_9
    | 10, _ => s3_10
    | 11, _ => s3_11
    | _ + 12, h => absurd h (by omega)

/-- **Refchecks accepted, so the owner's method runs.** On the membership space, for scalac 2.12,
2.13 and dotc 3.9: `Members` accepts exactly what the compiler accepts; for an accepted program and
each concrete class `C` with owner `O`, HotSpot ran `O`'s `m` (except `bug13199` under Scala 2), and the
lowered program linked by `Jvm` runs `O`'s lowered method (except `lowerGap`), so no
`AbstractMethodError`. -/
theorem refchecks_sound : ∀ dl ∈ [Dialect.s212, .s213, .s3], space.all (holds dl) = true := by
  intro dl h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact holds_s212
  · exact holds_s213
  · exact holds_s3

/-- The counterexamples: Scala 2 accepts the four `bug13199` programs and HotSpot throws
`AbstractMethodError`; dotc rejects them. -/
theorem bug13199_witnesses :
    bug13199.all (fun i => (Members.membersSpace[i]?).any fun x =>
      accepts .s212 x.2 && accepts .s213 x.2 && !accepts .s3 x.2) = true ∧
    bug13199.all (fun i => ranAt .s212 i "C" == some "!AbstractMethodError" &&
      ranAt .s213 i "C" == some "!AbstractMethodError") = true := by
  decide +kernel

end Scala.Refchecks
