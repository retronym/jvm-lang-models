/-!
# Scopes across phases: mutated, not copied

A class's declarations are asked *at a phase*: `exitingPhase(p)(cls.info.decls)` in scalac,
`atPhase(p)(cls.info.decls)` in dotc. Neither compiler copies a class's `Scope` at every phase.
A scope is one mutable object, shared by a run of phases: scalac starts a new one only when an info
transformer builds a new `ClassInfoType` with a new scope (`decls.cloneScope`, `newScope`), and
dotc only when a phase installs a new denotation (`enteredAfter`, `installAfter`). A phase that
enters a member into "the" scope mutates whichever object is current at the phase it names.

So a member is visible, after the run, from the start of the scope version it landed in, not from
the phase that meant to add it. The obligation on a compiler that mutates scopes is that every
entry lands in a version that starts exactly where the member should become visible. dotc's
`enteredAfter(thisPhase)` meets it by construction: it installs a version starting at the next
phase and enters there. scalac's LambdaLift does not, and says so:

> this modifies the ClassInfotype of the enclosing class, which is associated with another phase

(`LambdaLift.scala`, a TODO above `sym.owner.info.decls enterUnique sym`.) The measurements are
`packages/scala/probes/phases`: each class's declarations recorded during the run at each phase,
and asked again after it.

Phases are numbered as `-Xshow-phases` numbers them in scalac 2.13.18; a version "starts at `n`"
when it is the answer for reads entering phase `n` (that is, exiting phase `n - 1`).
-/

namespace ScalaTypes.Scopes

/-! ## The abstract statement -/

/-- The start of the scope version that holds phase `t`: the latest start at or before `t`, or `0`
(the version the namer made). -/
def start (starts : List Nat) (t : Nat) : Nat := (starts.filter (· ≤ t)).foldl max 0

/-- A member entered by a phase. `vis` is the first phase that should see it; `tgt` is the phase
whose scope the entering code mutates (the current phase for `info.decls enter`, the next phase
for `enteredAfter(thisPhase)` or scalac's `afterOwnPhase`). -/
structure Entry where
  name : String
  vis : Nat
  tgt : Nat
  deriving DecidableEq, Repr

/-- The intended answer at phase `q`. -/
def truth (es : List Entry) (q : Nat) : List Entry := es.filter (·.vis ≤ q)

/-- The answer after the run: an entry is in every version from the one it landed in. (Assumes
each version was copied after the entries of the versions before it; `run` drops that.) -/
def late (starts : List Nat) (es : List Entry) (q : Nat) : List Entry :=
  es.filter (start starts ·.tgt ≤ q)

/-- **The obligation.** Late answers equal the intended ones at every phase iff each entry lands
in a version that starts exactly at the phase from which it should be visible. -/
theorem late_eq_truth_iff (starts : List Nat) (es : List Entry) :
    (∀ q, late starts es q = truth es q) ↔ ∀ e ∈ es, start starts e.tgt = e.vis := by
  constructor
  · intro h e he
    have iff : ∀ q, start starts e.tgt ≤ q ↔ e.vis ≤ q := by
      intro q
      have hq := h q
      constructor
      · intro hs
        have : e ∈ late starts es q := List.mem_filter.2 ⟨he, by simpa using hs⟩
        rw [hq] at this
        simpa using (List.mem_filter.1 this).2
      · intro hv
        have : e ∈ truth es q := List.mem_filter.2 ⟨he, by simpa using hv⟩
        rw [← hq] at this
        simpa using (List.mem_filter.1 this).2
    have h1 := (iff (start starts e.tgt)).1 (Nat.le_refl _)
    have h2 := (iff e.vis).2 (Nat.le_refl _)
    omega
  · intro h q
    unfold late truth
    apply List.filter_congr
    intro e he
    rw [h e he]

theorem foldl_max_le (b : Nat) : ∀ (l : List Nat) (acc : Nat), acc ≤ b → (∀ x ∈ l, x ≤ b) →
    l.foldl max acc ≤ b
  | [], _, h, _ => h
  | x :: xs, acc, h, hl => foldl_max_le b xs _ (Nat.max_le.2 ⟨h, hl x (by simp)⟩)
      fun y hy => hl y (by simp [hy])

theorem le_foldl_max : ∀ (l : List Nat) (acc x : Nat), (x ∈ l ∨ x ≤ acc) → x ≤ l.foldl max acc
  | [], _, _, h => by simpa using h
  | y :: ys, acc, x, h => le_foldl_max ys _ x (by
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · right; exact Nat.le_max_right _ _
        · left; exact h
      · right; exact Nat.le_trans h (Nat.le_max_left _ _))

/-- dotc's discipline: `enteredAfter(thisPhase)` at phase `p` installs a version starting at
`p + 1` and enters the member there, so it lands exactly where it should be visible. -/
theorem enteredAfter_sound (starts : List Nat) (p : Nat) (h : p + 1 ∈ starts) :
    start starts (p + 1) = p + 1 :=
  Nat.le_antisymm
    (foldl_max_le _ _ _ (Nat.zero_le _) fun x hx => by simpa using (List.mem_filter.1 hx).2)
    (le_foldl_max _ _ _ (Or.inl (List.mem_filter.2 ⟨h, by simp⟩)))

/-! ## Measured: scalac 2.13.18

`object C { def m: AnyRef = { class E; new E } }`. The module class's scope versions start at
`0` (namer), `11` (UnCurry's info transformer: answers exiting uncurry), `14` (SpecializeTypes'
info transformer copies every class it may specialize, `newScopeWith`) and `20` (Flatten builds a
`newScope`). LambdaLift (`17`) enters `E$1` into the scope current at `17`, version `14`: after the
run, `E$1` is a declaration exiting specialize, three phases before LambdaLift ran. With
`-no-specialization` SpecializeTypes leaves the type alone and the version is `11`: `E$1` is
there exiting uncurry. -/

def uncurry := 10
def specialize := 13
def lambdalift := 17
def flatten := 19
def mixin := 20

def liftedE : Entry := { name := "E$1", vis := lambdalift + 1, tgt := lambdalift }

/-- Default: `E$1` is in the late answer from exiting specialize (start `14`). -/
theorem lifted_from_specialize : start [0, 11, 14, 20] liftedE.tgt = specialize + 1 := by decide

/-- `-no-specialization`: from exiting uncurry (start `11`). -/
theorem lifted_from_uncurry : start [0, 11, 20] liftedE.tgt = uncurry + 1 := by decide

/-- Either way the obligation fails, so some earlier-phase answer changes after the run. -/
theorem lifted_unsound : ¬ ∀ q, late [0, 11, 14, 20] [liftedE] q = truth [liftedE] q := by
  rw [late_eq_truth_iff]; decide

/-- `class A extends T`, where `T` has a concrete `def t`: Mixin (`20`) enters the forwarder `t`
into the version Flatten made (start `20`), so it is a declaration exiting flatten. -/
theorem mixinForwarder_from_flatten :
    start [0, 11, 14, 20] ({ name := "t", vis := mixin + 1, tgt := mixin } : Entry).tgt = flatten + 1 := by
  decide

/-! ## Copies are lazy, so their timing matters

The abstract `late` assumes each version was copied after the entries of the versions before it.
scalac copies lazily: an info transformer runs when the info is first asked at or after its phase,
which a phase travel (`exitingFlatten { ... }`) can do early. A version copied before an entry
into its predecessor never gets it. dotc had this bug, [scala/scala3#440](https://github.com/scala/scala3/issues/440)
("`enteredAfter(phase.next)` makes all subsequent `enteredAfter(phase)` become lost"), and fixed it
by making an entry also enter later versions. `run` replays a sequence of copies and entries. -/

inductive Act
  /-- An info transformer makes the version starting at `c`, a copy of the one current at `c`. -/
  | copy (c : Nat)
  /-- A phase enters a member into the version current at `t`. -/
  | enter (t : Nat) (m : String)
  /-- A phase removes a member from the version current at `t` (dotc's `MoveStatics`). -/
  | drop (t : Nat) (m : String)
  deriving Repr

/-- Versions as `(start, members)`, any order. -/
abbrev Store := List (Nat × List String)

def Store.read (s : Store) (q : Nat) : List String :=
  ((s.lookup (start (s.map (·.1)) q)).getD [])

def Store.modify (s : Store) (t : Nat) (f : List String → List String) : Store :=
  let k := start (s.map (·.1)) t
  s.map fun (c, ms) => if c = k then (c, f ms) else (c, ms)

def Store.step (s : Store) : Act → Store
  | .copy c => (c, s.read c) :: s
  | .enter t m => s.modify t (· ++ [m])
  | .drop t m => s.modify t (·.erase m)

def run (acts : List Act) : Store := acts.foldl Store.step [(0, [])]

/-- In order: Flatten's copy after LambdaLift's entry. `E$1` is declared exiting flatten too. -/
theorem copy_after_entry :
    (run [.copy 11, .copy 14, .enter lambdalift "E$1", .copy 20]).read (flatten + 1) = ["E$1"] := by
  decide

/-- A phase travel forced Flatten's copy before LambdaLift ran: `E$1` is in the versions before
flatten and missing from flatten on, where the backend reads. -/
theorem copy_before_entry :
    (run [.copy 11, .copy 14, .copy 20, .enter lambdalift "E$1"]).read (flatten + 1) = [] ∧
    (run [.copy 11, .copy 14, .copy 20, .enter lambdalift "E$1"]).read (specialize + 1) = ["E$1"] := by
  decide

/-! ## Measured: dotc 3.9.0

dotc versions scopes, but a few transforms use `entered` (mutate the current denotation's scope)
instead of `enteredAfter`. With no new denotation since typer, the entry lands in the typer
version: `SpecializeFunctions` adds `apply$mcII$sp` to `class F extends (Int => Int)`, and an
`atPhase(typer)` read after the run sees it. `MoveStatics` moves `@static val t` from `object S`
to `class S` with `entered` and `unlink`: after the run, `S` has `t` and `S$` lacks it at typer. -/

/-- dotc phase ids are not scalac's; only the order matters here. -/
def dTyper := 4
def dMoveStatics := 70

theorem moveStatics_typer :
    let s := run [.enter 0 "t", .drop dMoveStatics "t"]
    s.read dTyper = [] := by decide

theorem moveStatics_enteredAfter :
    let s := run [.enter 0 "t", .copy (dMoveStatics + 1), .drop (dMoveStatics + 1) "t"]
    s.read dTyper = ["t"] ∧ s.read (dMoveStatics + 1) = [] := by decide

end ScalaTypes.Scopes
