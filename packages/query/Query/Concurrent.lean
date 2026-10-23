import Query.Lazy
import Query.Interrupt
/-!
# Two forcers over one lazy store

A presentation compiler that serves two requests at once is two evaluators over one symbol table:
Kotlin K2's lazy resolve under read actions, a parallel Haskell runtime's two evaluators meeting one
thunk (Harris, Marlow and Peyton Jones 2005). Over the facts of `Query.Lazy` the question is what a
black hole means when it has an owner. This file is the model for step 1 of the multi-reader plan
(the scala3 checkout's `interactive-multi-reader.md`, §7).

* **The machine** (§1). A store of finished facts, a hole per fact in progress tagged with the forcer
  that owns it, and two forcers, each a list of demands and a stack of frames (a fact and the rest
  of its rule). A scheduler step runs one forcer by one *force step*: read a finished fact, enter a
  rule (take the hole), continue a rule with a value, publish a value (store it, release the hole),
  wait on the other forcer's hole, or unwind on a cycle. A rule's intermediate state is seen by its
  owner only: this is K2's `FirInProcessOfResolvingToPhaseStateWithBarrier`, and dotc's `Touched`
  with the thread that set it recorded.
* **Linearizability** (§2). `step_inv` and `run_agree`: for rules with a fixed point, under *every*
  schedule, every value the two forcers store or answer is the fixed point's, as a sequential
  `forceAll` would give (the concurrent `forceA_agree`). On the scenarios, by `decide` over every
  schedule: both forcers finish, and their answers and the store are the sequential ones.
* **Cycles** (§3). `run_ranked_no_cyc`: under a ranked fixed point no schedule ever reports a cycle,
  self or cross-thread, so a wait that would close a wait-for cycle is a dependency cycle of the
  rules (its contrapositive `waitCycle_unranked`), and raising `CyclicReference` in the forcer that
  closes it is sound. On the two signatures that need each other, forced from two forcers, every
  schedule reports both as cycles, as the sequential run does, and neither forcer deadlocks.
* **Peek** (§4). A peek that answers `absent` for a hole owned by the *other* forcer is a race:
  two schedules, two stored values of the same fact (`peek_any_races`). A peek that answers
  `absent` only for the forcer's own holes, and waits on the other's, gives every schedule the
  sequential answer (`peek_own_agrees`). The thirteen `isCompleting` sites must mean "on this
  reader".
* **Abort with a waiter** (§5). An owner unwound while the other forcer waits on its hole: with the
  hole released on unwinding, the waiter takes over and answers as a run without the owner would
  (`abort_waiter_takes_over`, the `abort_*` theorems of `Query.Interrupt` with a waiter); with
  dotc's discipline, the hole left set, the waiter waits for the rest of the run
  (`abort_keep_hole_waiter_stuck`).
-/

namespace Query.Concurrent

open Query.Lazy

variable {Q V : Type} [DecidableEq Q]

/-! ## 1. The machine -/

/-- The two forcers. -/
inductive Who | a | b
  deriving DecidableEq, Repr

def Who.other : Who → Who
  | .a => .b
  | .b => .a

theorem Who.other_of_ne {w w' : Who} (h : w' ≠ w) : w' = w.other := by
  cases w <;> cases w' <;> simp_all [Who.other]

/-- Which holes a peek sees as "in progress": `own`, the forcer's own only (the other's are waited
on like a force); `any`, either forcer's. -/
inductive PeekMode | own | any
  deriving DecidableEq, Repr

/-- A frame: the fact being forced and the rest of its rule, stopped at the question it asks next
(or at its value). -/
abbrev Frame (Q V : Type) := Q × Task (Probe Q) (fun _ => V) V

/-- A forcer: its demands still to answer (the head is the one in progress, if any frame is), its
stack of frames (top first), and the answers so far, each with its demand. -/
structure Forcer (Q V : Type) where
  demands : List Q
  frames : List (Frame Q V)
  results : List (Q × Out Q V)

/-- The shared state: the finished facts, the holes with their owners, the two forcers. -/
structure CSt (Q V : Type) where
  store : Store Q V
  holes : Q → Option Who
  fa : Forcer Q V
  fb : Forcer Q V

def CSt.get (st : CSt Q V) : Who → Forcer Q V
  | .a => st.fa
  | .b => st.fb

def CSt.set (st : CSt Q V) : Who → Forcer Q V → CSt Q V
  | .a, f => { st with fa := f }
  | .b, f => { st with fb := f }

/-- The fact a forcer needs next, if it is at a question: its top frame's question, or its next
demand when nothing is in progress. -/
def Forcer.wants : Forcer Q V → Option (Probe Q)
  | ⟨_, (_, .ask p _) :: _, _⟩ => some p
  | ⟨q :: _, [], _⟩ => some (.force q)
  | _ => none

/-- Release every hole owned by `w`. -/
def releaseAll (holes : Q → Option Who) (w : Who) : Q → Option Who :=
  fun q => if holes q = some w then none else holes q

/-- The forcer after its unwinding: frames dropped, its demand in progress answered `o`, or
dropped when `o` is `none` (an abort: the request is gone). -/
def unwindForcer (f : Forcer Q V) : Option (Out Q V) → Forcer Q V
  | some o => match f.demands with
    | q :: ds => ⟨ds, [], f.results ++ [(q, o)]⟩
    | [] => ⟨[], [], f.results⟩
  | none => ⟨f.demands.drop 1, [], f.results⟩

/-- Unwind forcer `w`: its frames are dropped, its holes released if `unlock` (K2 and the design's
§3.1: an unwound completion leaves the symbol completable; dotc's `Touched` without a reset is
`unlock = false`), and its demand in progress is answered `o`, or dropped when `o` is `none`. -/
def unwind (unlock : Bool) (w : Who) (o : Option (Out Q V)) (st : CSt Q V) : CSt Q V :=
  { (st.set w (unwindForcer (st.get w) o)) with
      holes := if unlock then releaseAll st.holes w else st.holes }

/-- Does `w`'s waiting on fact `q`, held by the other forcer, close a wait-for cycle: is the other
forcer waiting on a fact `w` holds? Each forcer waits on at most one fact, so following the owner of
the hole back is the whole check (the design's §4.2; Salsa's cross-thread cycle detection). -/
def closesCycle (st : CSt Q V) (w : Who) : Bool :=
  match (st.get w.other).wants with
  | some p => st.holes (Interrupt.fact p) = some w
  | none => false

/-- Forcer `w` needs fact `q` (by a force, or by a peek that found no hole of its own): read it if
finished; wait if the other forcer holds it, unless that closes a wait-for cycle, which is a cyclic
reference raised here; a hole of its own is a cyclic reference; else take the hole and enter the
rule. `continue` is the forcer with the value in hand. -/
def want (R : PRules Q V) (unlock : Bool) (w : Who) (q : Q) (st : CSt Q V) : CSt Q V :=
  match st.store q with
  | some _ => st     -- a finished fact: the next step of this forcer reads it (`continueWith`)
  | none =>
    match st.holes q with
    | some w' =>
      if w' = w then unwind unlock w (some (.cyc q)) st
      else if closesCycle st w then unwind unlock w (some (.cyc q)) st
      else st        -- wait on the barrier
    | none =>
      { (st.set w { st.get w with frames := (q, R q) :: (st.get w).frames }) with
          holes := fun q' => if q' = q then some w else st.holes q' }

/-- Does a question `p` at a fact in progress answer `absent`: a peek, at a hole the mode lets it
see. -/
def peeksAbsent (mode : PeekMode) (w : Who) : Probe Q → Option Who → Bool
  | .peek _, some w' => decide (mode = .any) || decide (w' = w)
  | _, _ => false

/-- One force step of forcer `w`. -/
def step (R : PRules Q V) (mode : PeekMode) (unlock : Bool) (absent : V) (w : Who) (st : CSt Q V) :
    CSt Q V :=
  match (st.get w).frames with
  | [] =>
    match (st.get w).demands with
    | [] => st
    | q :: ds =>
      match st.store q with
      | some v => st.set w ⟨ds, [], (st.get w).results ++ [(q, .ok v)]⟩   -- the demand's value, published
      | none => want R unlock w q st
  | (q, .pure v) :: rest =>                                        -- publish: store, release the hole
    { (st.set w { st.get w with frames := rest }) with
        store := upd st.store q v,
        holes := fun q' => if q' = q then none else st.holes q' }
  | (q, .ask p k) :: rest =>
    match st.store (Interrupt.fact p) with
    | some v => st.set w { st.get w with frames := (q, k v) :: rest }    -- continue with the value
    | none =>
      if peeksAbsent mode w p (st.holes (Interrupt.fact p)) then
        st.set w { st.get w with frames := (q, k absent) :: rest }
      else want R unlock w (Interrupt.fact p) st

/-- A scheduler's action: a force step of one forcer, or its abort (a cancellation unwinding it). -/
inductive Act | run (w : Who) | abort (w : Who)
  deriving DecidableEq, Repr

def act (R : PRules Q V) (mode : PeekMode) (unlock : Bool) (absent : V) (st : CSt Q V) : Act → CSt Q V
  | .run w => step R mode unlock absent w st
  | .abort w => unwind unlock w none st

def runActs (R : PRules Q V) (mode : PeekMode) (unlock : Bool) (absent : V) :
    List Act → CSt Q V → CSt Q V
  | [], st => st
  | x :: xs, st => runActs R mode unlock absent xs (act R mode unlock absent st x)

/-- The initial state: two demand lists, an empty store. -/
def init (da db : List Q) : CSt Q V :=
  ⟨fun _ => none, fun _ => none, ⟨da, [], []⟩, ⟨db, [], []⟩⟩

/-- Both forcers have answered every demand. -/
def CSt.idle (st : CSt Q V) : Bool :=
  st.fa.demands.isEmpty && st.fa.frames.isEmpty && st.fb.demands.isEmpty && st.fb.frames.isEmpty

/-- Alternate the two forcers for `n` steps each: the fair tail of a schedule. -/
def roundRobin (n : Nat) : List Act :=
  (List.replicate n [Act.run .a, Act.run .b]).flatten

/-- Every schedule of `n` steps. -/
def scheds : Nat → List (List Act)
  | 0 => [[]]
  | n + 1 => (scheds n).flatMap fun s => [Act.run .a :: s, Act.run .b :: s]

/-- A schedule prefix of `n` steps, then the fair tail long enough to finish. -/
def runSched (R : PRules Q V) (mode : PeekMode) (unlock : Bool) (absent : V) (da db : List Q)
    (fuel : Nat) (s : List Act) : CSt Q V :=
  runActs R mode unlock absent (s ++ roundRobin fuel) (init da db)

/-- The store read at a list of facts, for `decide`. -/
def CSt.read (st : CSt Q V) (qs : List Q) : List (Option V) := qs.map st.store

/-! ## 2. Linearizability: every schedule agrees with the sequential semantics

The invariant is the one inside `force_ok`, read over the frames: a frame's task is the rest of its
rule after questions answered with the fixed point's values, so the value it publishes is the
rule's value. Nothing about the schedule enters. -/

/-- `t` is `t₀` after some of its questions, answered by `e`. -/
inductive Reach {Q : Type} {A : Q → Type} {α : Type} (e : Task.Env Q A) :
    Task Q A α → Task Q A α → Prop
  | refl (t : Task Q A α) : Reach e t t
  | ask {q : Q} {k : A q → Task Q A α} {t : Task Q A α} :
      Reach e (k (e q)) t → Reach e (.ask q k) t

omit [DecidableEq Q] in
theorem Reach.run {A : Q → Type} {α : Type} {e : Task.Env Q A} {t₀ t : Task Q A α}
    (h : Reach e t₀ t) : t₀.run e = t.run e := by
  induction h with
  | refl _ => rfl
  | ask _ ih => rw [Task.run_ask]; exact ih

omit [DecidableEq Q] in
theorem Reach.mem_trace {A : Q → Type} {α : Type} {e : Task.Env Q A} {t₀ t : Task Q A α}
    (h : Reach e t₀ t) {q : Q} {k : A q → Task Q A α} (ht : t = .ask q k) : q ∈ t₀.trace e := by
  induction h with
  | refl _ => subst ht; simp [Task.trace]
  | ask _ ih => simp only [Task.trace_ask, List.mem_cons]; exact Or.inr (ih ht)

omit [DecidableEq Q] in
theorem Reach.step' {A : Q → Type} {α : Type} {e : Task.Env Q A} {t₀ t : Task Q A α}
    (h : Reach e t₀ t) {q : Q} {k : A q → Task Q A α} (ht : t = .ask q k) : Reach e t₀ (k (e q)) := by
  induction h with
  | refl _ => subst ht; exact .ask (.refl _)
  | ask _ ih => exact .ask (ih ht)

omit [DecidableEq Q] in
theorem Reach.step {A : Q → Type} {α : Type} {e : Task.Env Q A} {t₀ : Task Q A α} {q : Q}
    {k : A q → Task Q A α} (h : Reach e t₀ (.ask q k)) : Reach e t₀ (k (e q)) := h.step' rfl

/-- A task that only forces. -/
inductive NoPeek : Task (Probe Q) (fun _ => V) V → Prop
  | pure (v : V) : NoPeek (.pure v)
  | ask (q : Q) (k : V → Task (Probe Q) (fun _ => V) V) (h : ∀ v, NoPeek (k v)) :
      NoPeek (.ask (.force q) k)

omit [DecidableEq Q] in
theorem NoPeek.reach {e : Task.Env (Probe Q) (fun _ => V)} {t₀ t : Task (Probe Q) (fun _ => V) V}
    (h : Reach e t₀ t) (h₀ : NoPeek t₀) : NoPeek t := by
  induction h with
  | refl _ => exact h₀
  | ask _ ih => cases h₀ with | ask _ _ hk => exact ih (hk _)

/-- The invariant: the store agrees with `ρ`, every frame is the rest of its rule under `ρ`, and
every answer given is `ρ`'s. -/
def Inv (R : PRules Q V) (ρ : Q → V) (st : CSt Q V) : Prop :=
  Agree ρ st.store ∧
  (∀ w, ∀ fr ∈ (st.get w).frames, Reach (Interrupt.probeEnv ρ) (R fr.1) fr.2) ∧
  (∀ w, ∀ r ∈ (st.get w).results, ∀ v, r.2 = .ok v → v = ρ r.1)

omit [DecidableEq Q] in
theorem CSt.get_set_same (st : CSt Q V) (w : Who) (f : Forcer Q V) : (st.set w f).get w = f := by
  cases w <;> rfl

omit [DecidableEq Q] in
theorem CSt.get_set_other (st : CSt Q V) (w w' : Who) (f : Forcer Q V) (h : w' ≠ w) :
    (st.set w f).get w' = st.get w' := by
  cases w <;> cases w' <;> first | exact absurd rfl h | rfl

omit [DecidableEq Q] in
theorem CSt.get_holes (x : CSt Q V) (hs : Q → Option Who) (w : Who) :
    ({ x with holes := hs } : CSt Q V).get w = x.get w := by cases w <;> rfl

omit [DecidableEq Q] in
theorem CSt.get_store_holes (x : CSt Q V) (s : Store Q V) (hs : Q → Option Who) (w : Who) :
    ({ x with store := s, holes := hs } : CSt Q V).get w = x.get w := by cases w <;> rfl

omit [DecidableEq Q] in
theorem CSt.store_set (st : CSt Q V) (w : Who) (f : Forcer Q V) : (st.set w f).store = st.store := by
  cases w <;> rfl

omit [DecidableEq Q] in
/-- Changing one forcer keeps the invariant when the new forcer meets its two clauses. -/
theorem Inv.set (R : PRules Q V) (ρ : Q → V) {st : CSt Q V} (h : Inv R ρ st) (w : Who) (f : Forcer Q V)
    (hf : ∀ fr ∈ f.frames, Reach (Interrupt.probeEnv ρ) (R fr.1) fr.2)
    (hr : ∀ r ∈ f.results, ∀ v, r.2 = .ok v → v = ρ r.1) : Inv R ρ (st.set w f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [CSt.store_set]; exact h1, fun w' => ?_, fun w' => ?_⟩
  · by_cases hw : w' = w
    · subst hw; rw [CSt.get_set_same]; exact hf
    · rw [CSt.get_set_other _ _ _ _ hw]; exact h2 w'
  · by_cases hw : w' = w
    · subst hw; rw [CSt.get_set_same]; exact hr
    · rw [CSt.get_set_other _ _ _ _ hw]; exact h3 w'

omit [DecidableEq Q] in
theorem Inv.holes (R : PRules Q V) (ρ : Q → V) {st : CSt Q V} (h : Inv R ρ st) (hs : Q → Option Who) :
    Inv R ρ { st with holes := hs } := h

omit [DecidableEq Q] in
theorem unwindForcer_frames (f : Forcer Q V) (o : Option (Out Q V)) : (unwindForcer f o).frames = [] := by
  unfold unwindForcer; split <;> (try split) <;> rfl

omit [DecidableEq Q] in
theorem unwindForcer_results (f : Forcer Q V) (o : Option (Out Q V)) :
    ∀ r ∈ (unwindForcer f o).results, r ∈ f.results ∨ ∃ o', o = some o' ∧ r.2 = o' := by
  intro r hr
  unfold unwindForcer at hr
  split at hr
  · split at hr
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl hr
  · exact Or.inl hr

omit [DecidableEq Q] in
theorem unwind_get_same (unlock : Bool) (w : Who) (o : Option (Out Q V)) (st : CSt Q V) :
    (unwind unlock w o st).get w = unwindForcer (st.get w) o := by
  cases w <;> rfl

omit [DecidableEq Q] in
theorem unwind_get_other (unlock : Bool) (w w' : Who) (o : Option (Out Q V)) (st : CSt Q V) (h : w' ≠ w) :
    (unwind unlock w o st).get w' = st.get w' := by
  cases w <;> cases w' <;> first | exact absurd rfl h | rfl

omit [DecidableEq Q] in
theorem unwind_holes (unlock : Bool) (w : Who) (o : Option (Out Q V)) (st : CSt Q V) :
    (unwind unlock w o st).holes = if unlock then releaseAll st.holes w else st.holes := by
  cases w <;> rfl

omit [DecidableEq Q] in
theorem unwind_inv (R : PRules Q V) (ρ : Q → V) (unlock : Bool) (w : Who) (o : Option (Out Q V))
    {st : CSt Q V} (h : Inv R ρ st) (ho : ∀ v, o ≠ some (.ok v)) : Inv R ρ (unwind unlock w o st) := by
  unfold unwind
  apply Inv.holes
  apply Inv.set R ρ h
  · rw [unwindForcer_frames]; simp
  · intro r hr v hv
    rcases unwindForcer_results _ _ r hr with hr | ⟨o', rfl, ho'⟩
    · exact h.2.2 w r hr v hv
    · rw [ho'] at hv; exact absurd (congrArg some hv) (ho v)

theorem want_inv (R : PRules Q V) (ρ : Q → V) (unlock : Bool) (w : Who) (q : Q) {st : CSt Q V}
    (h : Inv R ρ st) : Inv R ρ (want R unlock w q st) := by
  unfold want
  split
  · exact h
  · split
    · split
      · exact unwind_inv R ρ unlock w _ h (fun v hv => by cases hv)
      · split
        · exact unwind_inv R ρ unlock w _ h (fun v hv => by cases hv)
        · exact h
    · apply Inv.holes
      apply Inv.set R ρ h
      · intro fr hfr
        simp only [List.mem_cons] at hfr
        rcases hfr with rfl | hfr
        · exact .refl _
        · exact h.2.1 w fr hfr
      · exact h.2.2 w

/-- **Every step keeps the invariant**, for rules that only force, with a fixed point. -/
theorem step_inv (R : PRules Q V) (ρ : Q → V) (hfix : Interrupt.PFix R ρ)
    (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (unlock : Bool) (absent : V) (w : Who)
    {st : CSt Q V} (h : Inv R ρ st) : Inv R ρ (step R mode unlock absent w st) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold step
  split
  · -- no frame: a demand
    rename_i hfr
    split
    · exact ⟨h1, h2, h3⟩
    · rename_i q ds hd
      split
      · rename_i v hv
        apply Inv.set R ρ ⟨h1, h2, h3⟩
        · intro fr hfr; simp at hfr
        · intro r hr v' hv'
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | hr
          · exact h3 w r hr v' hv'
          · subst hr; simp only [Out.ok.injEq] at hv'; subst hv'; exact h1 q v hv
      · exact want_inv R ρ unlock w q ⟨h1, h2, h3⟩
  · -- publish
    rename_i q v rest hfr
    have hre : Reach (Interrupt.probeEnv ρ) (R q) (.pure v) := h2 w (q, .pure v) (by rw [hfr]; simp)
    have hv : v = ρ q := by
      have := hre.run
      simp only [Task.run_pure] at this
      rw [← this, ← hfix q]
    refine ⟨?_, fun w' => ?_, fun w' => ?_⟩
    · intro x y hx
      simp only [upd] at hx
      split at hx
      · subst_vars; injection hx with hx; exact hx.symm
      · exact h1 x y hx
    · by_cases hw : w' = w
      · subst hw
        show ∀ fr ∈ ((st.set w' _).get w').frames, _
        rw [CSt.get_set_same]
        intro fr hfr'
        exact h2 w' fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr')
      · show ∀ fr ∈ ((st.set w _).get w').frames, _
        rw [CSt.get_set_other _ _ _ _ hw]; exact h2 w'
    · by_cases hw : w' = w
      · subst hw
        show ∀ r ∈ ((st.set w' _).get w').results, _
        rw [CSt.get_set_same]; exact h3 w'
      · show ∀ r ∈ ((st.set w _).get w').results, _
        rw [CSt.get_set_other _ _ _ _ hw]; exact h3 w'
  · -- a question
    rename_i q p k rest hfr
    have hre : Reach (Interrupt.probeEnv ρ) (R q) (.ask p k) := h2 w (q, .ask p k) (by rw [hfr]; simp)
    have hnp' : NoPeek (Task.ask p k) := NoPeek.reach hre (hnp q)
    obtain ⟨q', hq'⟩ : ∃ q', p = .force q' := by cases hnp' with | ask q' _ _ => exact ⟨q', rfl⟩
    subst hq'
    split
    · rename_i v hv
      apply Inv.set R ρ ⟨h1, h2, h3⟩
      · intro fr hfr'
        simp only [List.mem_cons] at hfr'
        rcases hfr' with rfl | hfr'
        · have := hre.step
          simp only [Interrupt.probeEnv, Interrupt.fact] at this
          rw [h1 q' v hv]; exact this
        · exact h2 w fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr')
      · exact h3 w
    · split
      · rename_i hpk; simp [peeksAbsent] at hpk
      · exact want_inv R ρ unlock w q' ⟨h1, h2, h3⟩

theorem act_inv (R : PRules Q V) (ρ : Q → V) (hfix : Interrupt.PFix R ρ)
    (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (unlock : Bool) (absent : V) (x : Act)
    {st : CSt Q V} (h : Inv R ρ st) : Inv R ρ (act R mode unlock absent st x) := by
  cases x with
  | run w => exact step_inv R ρ hfix hnp mode unlock absent w h
  | abort w => exact unwind_inv R ρ unlock w none h (fun v hv => by cases hv)

theorem runActs_inv (R : PRules Q V) (ρ : Q → V) (hfix : Interrupt.PFix R ρ)
    (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (unlock : Bool) (absent : V) (xs : List Act)
    {st : CSt Q V} (h : Inv R ρ st) : Inv R ρ (runActs R mode unlock absent xs st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih (act_inv R ρ hfix hnp mode unlock absent x h)

omit [DecidableEq Q] in
theorem init_inv (R : PRules Q V) (ρ : Q → V) (da db : List Q) : Inv R ρ (init da db) := by
  unfold Inv
  refine ⟨fun _ _ h => (by cases h), ?_, ?_⟩
  · intro w; cases w <;> simp [init, CSt.get]
  · intro w; cases w <;> simp [init, CSt.get]

/-- **Linearizability.** For rules that only force and have a fixed point, under every schedule of
steps and aborts, with either peek mode and either unwinding discipline, the store agrees with the
fixed point and every answer either forcer gives is the fixed point's: whatever the interleaving,
the two forcers compute what one forcer computing both demand lists in sequence would
(`forceAll_ok`). The barrier is what makes it true: a forcer never reads a value that is not
published, and only the owner sees a rule in progress. -/
theorem run_agree (R : PRules Q V) (ρ : Q → V) (hfix : Interrupt.PFix R ρ)
    (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (unlock : Bool) (absent : V) (da db : List Q)
    (xs : List Act) :
    Agree ρ (runActs R mode unlock absent xs (init da db)).store ∧
    ∀ w, ∀ r ∈ ((runActs R mode unlock absent xs (init da db)).get w).results, ∀ v,
      r.2 = .ok v → v = ρ r.1 :=
  let h := runActs_inv R ρ hfix hnp mode unlock absent xs (init_inv R ρ da db)
  ⟨h.1, h.2.2⟩

/-! ## 3. Cycles: a wait-for cycle is a dependency cycle

With a ranking, the facts on a forcer's stack rank strictly downward from the demand to the
question at the top, and a hole is owned only while its fact is on its owner's stack. A self cycle
would put the question's fact on the stack above it; a wait-for cycle would rank each forcer's
question below the other's. Neither can happen, so under a ranked fixed point no schedule reports a
cycle, and a cycle reported is a cycle of the rules. -/

/-- Strictly increasing rank from the top of the stack down. -/
def RankedStack (r : Q → Nat) : List (Frame Q V) → Prop
  | [] => True
  | [_] => True
  | f₁ :: f₂ :: rest => r f₁.1 < r f₂.1 ∧ RankedStack r (f₂ :: rest)

omit [DecidableEq Q] in
theorem RankedStack.tail (r : Q → Nat) {f : Frame Q V} {rest : List (Frame Q V)}
    (h : RankedStack r (f :: rest)) : RankedStack r rest := by
  cases rest with
  | nil => trivial
  | cons f₂ rest => exact h.2

omit [DecidableEq Q] in
theorem RankedStack.top_le (r : Q → Nat) {f : Frame Q V} {rest : List (Frame Q V)}
    (h : RankedStack r (f :: rest)) : ∀ g ∈ f :: rest, r f.1 ≤ r g.1 := by
  induction rest generalizing f with
  | nil => intro g hg; simp at hg; subst hg; exact Nat.le_refl _
  | cons f₂ rest ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_of_lt h.1) (ih h.2 g hg')

/-- The invariant with a ranking: the stacks rank downward, each question is ranked below its
frame, and a hole's owner has its fact on the stack. -/
def RInv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (st : CSt Q V) : Prop :=
  Inv R ρ st ∧
  (∀ w, RankedStack r (st.get w).frames) ∧
  (∀ w, ∀ fr ∈ (st.get w).frames, ∀ p k, fr.2 = .ask p k → r (Interrupt.fact p) < r fr.1) ∧
  (∀ q w, st.holes q = some w → q ∈ (st.get w).frames.map Prod.fst)

/-- No `.cyc` among the results. -/
def NoCyc (st : CSt Q V) : Prop := ∀ w, ∀ r ∈ (st.get w).results, ∀ q, r.2 ≠ .cyc q

omit [DecidableEq Q] in
theorem CSt.holes_set (st : CSt Q V) (w : Who) (f : Forcer Q V) : (st.set w f).holes = st.holes := by
  cases w <;> rfl

omit [DecidableEq Q] in
/-- The fact a forcer wants is ranked below everything on its stack. -/
theorem RInv.wants_lt (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) {st : CSt Q V} (h : RInv R ρ r st)
    (w : Who) (p : Probe Q) (hp : (st.get w).wants = some p) :
    ∀ q ∈ (st.get w).frames.map Prod.fst, r (Interrupt.fact p) < r q := by
  obtain ⟨_, h2, h3, _⟩ := h
  have h2w := h2 w
  have h3w := h3 w
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨fr, hfr, rfl⟩ := hq
  rcases hf : (st.get w) with ⟨ds, frames, rs⟩
  rw [hf] at hp hfr h2w h3w
  simp only at hp hfr h2w h3w
  cases frames with
  | nil => simp at hfr
  | cons f₀ rest =>
    obtain ⟨q₀, t₀⟩ := f₀
    cases t₀ with
    | pure v => simp [Forcer.wants] at hp
    | ask p₀ k =>
      simp only [Forcer.wants, Option.some.injEq] at hp
      subst hp
      have hlt := h3w (q₀, .ask p₀ k) (by simp) p₀ k rfl
      have hle := h2w.top_le r fr hfr
      simp only at hlt hle
      omega

omit [DecidableEq Q] in
theorem unwind_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (w : Who) (o : Option (Out Q V))
    {st : CSt Q V} (h : RInv R ρ r st) (ho : ∀ v, o ≠ some (.ok v)) : RInv R ρ r (unwind true w o st) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨unwind_inv R ρ true w o h1 ho, fun w' => ?_, fun w' => ?_, fun q w' hq => ?_⟩
  · by_cases hw : w' = w
    · subst hw; rw [unwind_get_same, unwindForcer_frames]; trivial
    · rw [unwind_get_other _ _ _ _ _ hw]; exact h2 w'
  · by_cases hw : w' = w
    · subst hw; rw [unwind_get_same, unwindForcer_frames]; simp
    · rw [unwind_get_other _ _ _ _ _ hw]; exact h3 w'
  · rw [unwind_holes] at hq
    simp only [↓reduceIte, releaseAll] at hq
    split at hq
    · cases hq
    · rename_i hne
      have hw : w' ≠ w := fun e => hne (e ▸ hq)
      rw [unwind_get_other _ _ _ _ _ hw]
      exact h4 q w' hq

theorem want_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (w : Who) (q : Q) {st : CSt Q V}
    (h : RInv R ρ r st) (hwants : (st.get w).wants = some (.force q) ∨ ∃ p, (st.get w).wants = some p ∧ Interrupt.fact p = q)
    (hr : ∀ q' ∈ (R q).trace (Interrupt.probeEnv ρ), r (Interrupt.fact q') < r q) :
    RInv R ρ r (want R true w q st) := by
  have hlt : ∀ x ∈ (st.get w).frames.map Prod.fst, r q < r x := by
    rcases hwants with hw | ⟨p, hp, rfl⟩
    · have := RInv.wants_lt R ρ r h w _ hw; simpa [Interrupt.fact] using this
    · exact RInv.wants_lt R ρ r h w p hp
  have hinv : Inv R ρ (want R true w q st) := want_inv R ρ true w q h.1
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold want at hinv ⊢
  split
  · exact ⟨h1, h2, h3, h4⟩
  · rename_i hs
    split
    · split
      · exact unwind_rinv R ρ r w _ ⟨h1, h2, h3, h4⟩ (fun v hv => by cases hv)
      · split
        · exact unwind_rinv R ρ r w _ ⟨h1, h2, h3, h4⟩ (fun v hv => by cases hv)
        · exact ⟨h1, h2, h3, h4⟩
    · rename_i hnone
      simp only [hs, hnone] at hinv
      unfold RInv
      refine ⟨hinv, ?_, ?_, ?_⟩
      · intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [CSt.get_store_holes, CSt.get_set_same]
          rcases hf : (st.get w').frames with _ | ⟨f₂, rest⟩
          · trivial
          · refine ⟨hlt f₂.1 (by rw [hf]; simp), ?_⟩
            have := h2 w'; rw [hf] at this; exact this
        · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact h2 w'
      · intro w' fr hfr p k hpk
        by_cases hw : w' = w
        · subst hw
          simp only [CSt.get_store_holes, CSt.get_set_same, List.mem_cons] at hfr
          rcases hfr with rfl | hfr
          · simp only at hpk
            exact hr p (by rw [hpk]; simp [Task.trace])
          · exact h3 w' fr hfr p k hpk
        · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw] at hfr; exact h3 w' fr hfr p k hpk
      · intro x w' hx
        simp only at hx
        split at hx
        · subst_vars; injection hx with hx; subst hx
          simp [CSt.get_store_holes, CSt.get_set_same]
        · have := h4 x w' hx
          by_cases hw : w' = w
          · subst hw; simp only [CSt.get_store_holes, CSt.get_set_same, List.map_cons, List.mem_cons]; exact Or.inr this
          · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact this

/-- **Every step keeps the ranked invariant and reports no cycle**, under a ranked fixed point of
rules that only force, with holes released on unwinding. -/
theorem step_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (hfix : Interrupt.PFix R ρ)
    (hr : Interrupt.PRanked R ρ r) (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (absent : V) (w : Who)
    {st : CSt Q V} (h : RInv R ρ r st) (hc : NoCyc st) :
    RInv R ρ r (step R mode true absent w st) ∧ NoCyc (step R mode true absent w st) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  -- the two cases of `want` that unwind with a cycle are impossible
  have want_ok : ∀ q, (st.get w).wants = some (.force q) ∨ (∃ p, (st.get w).wants = some p ∧ Interrupt.fact p = q) →
      st.store q = none → NoCyc (want R true w q st) := by
    intro q hw hs
    have hlt : ∀ x ∈ (st.get w).frames.map Prod.fst, r q < r x := by
      rcases hw with hw | ⟨p, hp, rfl⟩
      · have := RInv.wants_lt R ρ r ⟨h1, h2, h3, h4⟩ w _ hw; simpa [Interrupt.fact] using this
      · exact RInv.wants_lt R ρ r ⟨h1, h2, h3, h4⟩ w p hp
    unfold want
    rw [hs]
    simp only
    split
    · rename_i w' hw'
      split
      · -- self: q is on w's own stack, ranked above itself
        rename_i heq
        rw [heq] at hw'
        exfalso
        have := hlt q (h4 q w hw')
        omega
      · split
        · -- cross: the other waits on a fact w holds, ranked below w's question, and vice versa
          rename_i hne hclose
          exfalso
          have hwo : w' = w.other := Who.other_of_ne hne
          subst hwo
          unfold closesCycle at hclose
          split at hclose
          · rename_i p' hp'
            simp only [decide_eq_true_eq] at hclose
            have h_a := hlt (Interrupt.fact p') (h4 _ w hclose)
            have h_b := RInv.wants_lt R ρ r ⟨h1, h2, h3, h4⟩ w.other p' hp' q (h4 q w.other hw')
            omega
          · cases hclose
        · exact hc
    · intro w' rr hrr
      by_cases hww : w' = w
      · subst hww; simp only [CSt.get_store_holes, CSt.get_set_same] at hrr; exact hc w' rr hrr
      · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hww] at hrr; exact hc w' rr hrr
  unfold step
  split
  · rename_i hfr
    split
    · exact ⟨⟨h1, h2, h3, h4⟩, hc⟩
    · rename_i q ds hd
      split
      · rename_i v hv
        refine ⟨⟨?_, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩, fun w' rr hrr => ?_⟩
        · exact (step_inv R ρ hfix hnp mode true absent w h1 |> fun hh => by
            unfold step at hh; rw [hfr] at hh; simp only [hd, hv] at hh; exact hh)
        · by_cases hw : w' = w
          · subst hw; simp [CSt.get_set_same, RankedStack]
          · simp only [CSt.get_set_other _ _ _ _ hw]; exact h2 w'
        · by_cases hw : w' = w
          · subst hw; simp [CSt.get_set_same]
          · simp only [CSt.get_set_other _ _ _ _ hw]; exact h3 w'
        · rw [CSt.holes_set] at hx
          have := h4 x w' hx
          by_cases hw : w' = w
          · subst hw; rw [hfr] at this; simp at this
          · simp only [CSt.get_set_other _ _ _ _ hw]; exact this
        · by_cases hw : w' = w
          · subst hw
            simp only [CSt.get_set_same, List.mem_append, List.mem_singleton] at hrr
            rcases hrr with hrr | rfl
            · exact hc w' rr hrr
            · simp
          · simp only [CSt.get_set_other _ _ _ _ hw] at hrr; exact hc w' rr hrr
      · rename_i hs
        have hw : (st.get w).wants = some (.force q) := by
          rcases hf : st.get w with ⟨ds', fr', rs'⟩
          rw [hf] at hfr hd; simp only at hfr hd; subst hfr hd; rfl
        exact ⟨want_rinv R ρ r w q ⟨h1, h2, h3, h4⟩ (Or.inl hw) (hr q), want_ok q (Or.inl hw) hs⟩
  · rename_i q v rest hfr
    have hinv := step_inv R ρ hfix hnp mode true absent w h1
    unfold step at hinv; rw [hfr] at hinv
    refine ⟨⟨hinv, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩, fun w' rr hrr => ?_⟩
    · by_cases hw : w' = w
      · subst hw; simp only [CSt.get_store_holes, CSt.get_set_same]; have := h2 w'; rw [hfr] at this; exact this.tail
      · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact h2 w'
    · by_cases hw : w' = w
      · subst hw; simp only [CSt.get_store_holes, CSt.get_set_same]
        intro fr hfr' p k hpk; exact h3 w' fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr') p k hpk
      · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact h3 w'
    · simp only at hx
      split at hx
      · cases hx
      · rename_i hne
        have := h4 x w' hx
        by_cases hw : w' = w
        · subst hw
          simp only [CSt.get_store_holes, CSt.get_set_same]
          rw [hfr] at this
          simp only [List.map_cons, List.mem_cons] at this
          rcases this with h | h
          · exact absurd h hne
          · exact h
        · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact this
    · by_cases hw : w' = w
      · subst hw; simp only [CSt.get_store_holes, CSt.get_set_same] at hrr; exact hc w' rr hrr
      · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw] at hrr; exact hc w' rr hrr
  · rename_i q p k rest hfr
    have hre : Reach (Interrupt.probeEnv ρ) (R q) (.ask p k) := h1.2.1 w (q, .ask p k) (by rw [hfr]; simp)
    have hnp' : NoPeek (Task.ask p k) := NoPeek.reach hre (hnp q)
    obtain ⟨q', hq'⟩ : ∃ q', p = .force q' := by cases hnp' with | ask q' _ _ => exact ⟨q', rfl⟩
    subst hq'
    have hw : (st.get w).wants = some (.force q') := by
      rcases hf : st.get w with ⟨ds', fr', rs'⟩
      rw [hf] at hfr; simp only at hfr; subst hfr; rfl
    split
    · rename_i v hv
      have hinv := step_inv R ρ hfix hnp mode true absent w h1
      unfold step at hinv; rw [hfr] at hinv; simp only [hv] at hinv
      refine ⟨⟨hinv, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩, fun w' rr hrr => ?_⟩
      · by_cases hww : w' = w
        · subst hww; simp only [CSt.get_set_same]
          have := h2 w'; rw [hfr] at this
          cases rest with
          | nil => trivial
          | cons f₂ rest => exact this
        · simp only [CSt.get_set_other _ _ _ _ hww]; exact h2 w'
      · by_cases hww : w' = w
        · subst hww; simp only [CSt.get_set_same]
          intro fr hfr' p' k' hpk
          simp only [List.mem_cons] at hfr'
          rcases hfr' with rfl | hfr'
          · simp only at hpk
            have hre' := hre.step
            simp only [Interrupt.probeEnv, Interrupt.fact] at hre'
            rw [h1.1 q' v hv] at hpk
            exact hr q p' (hre'.mem_trace hpk)
          · exact h3 w' fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr') p' k' hpk
        · simp only [CSt.get_set_other _ _ _ _ hww]; exact h3 w'
      · rw [CSt.holes_set] at hx
        have := h4 x w' hx
        by_cases hww : w' = w
        · subst hww; simp only [CSt.get_set_same]; rw [hfr] at this; simpa using this
        · simp only [CSt.get_set_other _ _ _ _ hww]; exact this
      · by_cases hww : w' = w
        · subst hww; simp only [CSt.get_set_same] at hrr; exact hc w' rr hrr
        · simp only [CSt.get_set_other _ _ _ _ hww] at hrr; exact hc w' rr hrr
    · rename_i hs
      split
      · rename_i hpk; simp [peeksAbsent] at hpk
      · exact ⟨want_rinv R ρ r w q' ⟨h1, h2, h3, h4⟩ (Or.inl hw) (hr q'), want_ok q' (Or.inl hw) hs⟩

omit [DecidableEq Q] in
theorem abort_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (w : Who) {st : CSt Q V}
    (h : RInv R ρ r st) (hc : NoCyc st) : RInv R ρ r (unwind true w none st) ∧ NoCyc (unwind true w none st) := by
  refine ⟨unwind_rinv R ρ r w none h (fun v hv => by cases hv), fun w' rr hrr => ?_⟩
  by_cases hw : w' = w
  · subst hw
    rw [unwind_get_same] at hrr
    rcases unwindForcer_results _ _ rr hrr with hrr | ⟨_, h', _⟩
    · exact hc w' rr hrr
    · cases h'
  · rw [unwind_get_other _ _ _ _ _ hw] at hrr; exact hc w' rr hrr

theorem runActs_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (hfix : Interrupt.PFix R ρ)
    (hr : Interrupt.PRanked R ρ r) (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (absent : V)
    (xs : List Act) {st : CSt Q V} (h : RInv R ρ r st) (hc : NoCyc st) :
    RInv R ρ r (runActs R mode true absent xs st) ∧ NoCyc (runActs R mode true absent xs st) := by
  induction xs generalizing st with
  | nil => exact ⟨h, hc⟩
  | cons x xs ih =>
    cases x with
    | run w =>
      obtain ⟨h', hc'⟩ := step_rinv R ρ r hfix hr hnp mode absent w h hc
      exact ih h' hc'
    | abort w =>
      obtain ⟨h', hc'⟩ := abort_rinv R ρ r w h hc
      exact ih h' hc'

omit [DecidableEq Q] in
theorem init_rinv (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (da db : List Q) : RInv R ρ r (init da db) := by
  unfold RInv
  refine ⟨init_inv R ρ da db, ?_, ?_, fun q w h => (by cases h)⟩
  · intro w; cases w <;> trivial
  · intro w; cases w <;> simp [init, CSt.get]

/-- **Under a ranked fixed point no schedule reports a cycle**, self or cross-thread: every
`.cyc` the machine can raise, including the one that closes a wait-for cycle, needs a fact ranked
below itself. So a wait-for cycle between the two forcers is a cycle of the rules
(`waitCycle_unranked`), and `CyclicReference` in the forcer that would close it is the right
report, as it is in the sequential evaluator (`cycle_unranked`). -/
theorem run_ranked_no_cyc (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (hfix : Interrupt.PFix R ρ)
    (hr : Interrupt.PRanked R ρ r) (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (absent : V)
    (da db : List Q) (xs : List Act) : NoCyc (runActs R mode true absent xs (init da db)) :=
  (runActs_rinv R ρ r hfix hr hnp mode absent xs (init_rinv R ρ r da db)
    (by intro w; cases w <;> simp [init, CSt.get])).2

/-- **A wait-for cycle is a dependency cycle.** If some schedule makes a forcer report a cycle
(the only way a wait can fail), the rules have no ranked fixed point. -/
theorem waitCycle_unranked (R : PRules Q V) (hnp : ∀ q, NoPeek (R q)) (mode : PeekMode) (absent : V)
    (da db : List Q) (xs : List Act) (w : Who) (q : Q) (rr : Q × Out Q V)
    (hm : rr ∈ ((runActs R mode true absent xs (init da db)).get w).results) (hc : rr.2 = .cyc q) :
    ∀ ρ r, Interrupt.PFix R ρ → ¬ Interrupt.PRanked R ρ r :=
  fun ρ r hfix hr => run_ranked_no_cyc R ρ r hfix hr hnp mode absent da db xs w rr hm q hc

/-! ## 4. The scenarios, by `decide` over every schedule

What the theorems leave open is progress: that every schedule *finishes*, with the demands
answered, which `decide` checks on the scenarios below, with the schedule's prefix free and a fair
tail. The scenarios are `Query.Interrupt`'s, as two demand lists. -/

/-- A force-only rule. -/
def forces (q : Q) (k : V → Task (Probe Q) (fun _ => V) V) : Task (Probe Q) (fun _ => V) V :=
  .ask (.force q) k

open Interrupt (Chain N3)

/-- `a → b → c → d`, as peeking rules without peeks. -/
def chainP : PRules Chain String
  | .a => forces .b fun v => .pure s!"a({v})"
  | .b => forces .c fun v => .pure s!"b({v})"
  | .c => forces .d fun v => .pure s!"c({v})"
  | .d => .pure "d"

/-- `a` asks `b`; `c` asks `a`. -/
def nested3P : PRules N3 String
  | .a => forces .b fun v => .pure s!"a({v})"
  | .b => .pure "b"
  | .c => forces .a fun v => .pure s!"c({v})"

/-- The sequential reference: both demand lists forced in order by one forcer. -/
def sequential (R : PRules Q V) (absent : V) (n : Nat) (da db : List Q) : List (Out Q V) × Store Q V :=
  forcePeekAll R absent n (da ++ db) (fun _ => none)

def CSt.answers (st : CSt Q V) : List (Out Q V) :=
  (st.fa.results ++ st.fb.results).map Prod.snd

/-- **The chain, forced from both ends by two forcers**: `a` by one, `c` by the other. The second
forcer takes `c` while the first is inside `b` and the first waits on it, or the first takes it and
the second waits; under all 64 schedules of six steps and a fair tail both finish, with the
sequential answers and the sequential store. -/
theorem chain_linearizable :
    ∀ s ∈ scheds 6,
      let st := runSched chainP .own true "absent" [.a] [.c] 30 s
      st.idle = true ∧ st.answers = (sequential chainP "absent" 9 [.a] [.c]).1 ∧
        st.read [.a, .b, .c, .d] = [.a, .b, .c, .d].map (sequential chainP "absent" 9 [.a] [.c]).2 := by
  decide +kernel

/-- **`nested_inside_frame_cycles`, with the request on its own forcer.** Serviced inside `a`'s
completer on the same thread the request for `c` black-holed on `a`; on a second forcer it waits on
`a`'s barrier and then answers. The interleaving that made a spurious cycle sequentially makes
none here. -/
theorem nested3_linearizable :
    ∀ s ∈ scheds 6,
      let st := runSched nested3P .own true "absent" [.a] [.c] 30 s
      st.idle = true ∧ st.answers = [.ok "a(b)", .ok "c(a(b))"] ∧
        st.read [.a, .b, .c] = [some "a(b)", some "b", some "c(a(b))"] := by
  decide +kernel

/-! ### The cross-thread cycle

`A`'s signature needs `B`'s and `B`'s needs `A`'s; a well-founded `c` beside them. Forced from two
forcers, one forcer waits on the other's hole and the other's wait would close the cycle: that
forcer reports `CyclicReference` and unwinds, releasing its hole; the waiter takes the hole over
and then meets its own hole, a cycle on one thread. Sequentially `forceAll [a, b]` reports both as
cycles too. -/

inductive X3 | a | b | c
  deriving DecidableEq, Repr

def crossP : PRules X3 String
  | .a => forces .b fun v => .pure s!"a({v})"
  | .b => forces .a fun v => .pure s!"b({v})"
  | .c => .pure "c"

/-- Both a cycle; neither forcer deadlocks; nothing on the cycle is stored, so the next request
recomputes it; `c` is stored. -/
theorem cross_cycle_both_report :
    ∀ s ∈ scheds 6,
      let st := runSched crossP .own true "absent" [.a, .c] [.b, .c] 30 s
      st.idle = true ∧
        (st.fa.results.map (fun r => match r.2 with | .cyc _ => true | _ => false)) = [true, false] ∧
        (st.fb.results.map (fun r => match r.2 with | .cyc _ => true | _ => false)) = [true, false] ∧
        st.read [.a, .b, .c] = [none, none, some "c"] := by
  decide +kernel

/-- The sequential run reports both as cycles as well. -/
theorem cross_cycle_sequential :
    (sequential crossP "absent" 9 [.a, .c] [.b, .c]).1 = [.cyc .a, .ok "c", .cyc .b, .ok "c"] := by
  decide

/-- **Where the cycle is reported depends on the schedule**, as sequentially it depends on the
order of demands. The first forcer taking `a` and then `b` meets its own hole at `a`: a cycle on
one thread, reported at `a`. The forcers alternating, each holding one signature: the first asks
`b`, held by the second, which is waiting on `a`, held by the first; that wait would close the
wait-for cycle, so the first reports the cycle at `b` and unwinds, and the second's wait succeeds. -/
theorem cross_cycle_report_site_varies :
    (runSched crossP .own true "absent" [.a] [.b] 30 [.run .a, .run .a, .run .b, .run .b]).fa.results =
      [(.a, .cyc .a)] ∧
    (runSched crossP .own true "absent" [.a] [.b] 30 [.run .a, .run .b, .run .a, .run .b]).fa.results =
      [(.a, .cyc .b)] := by
  decide +kernel

/-! ### Peek -/

/-- `a` peeks `c`; `c` asks `d`. Ranked (with the peek read as a force), so sequentially the peek
never sees `absent`. -/
inductive P3 | a | c | d
  deriving DecidableEq, Repr

def peekP : PRules P3 String
  | .a => .ask (.peek .c) fun v => .pure s!"a({v})"
  | .c => forces .d fun v => .pure s!"c({v})"
  | .d => .pure "d"

/-- **A peek at the other forcer's hole is a race.** The second forcer is inside `c` when the first
peeks it: `absent`, and `a = a(absent)` is published. The first forcer alone, or after the second
has published `c`: `a = a(c(d))`. Two schedules, two stored values of one fact, under ranked rules
where the sequential evaluator never peeks `absent` (`forcePeek_ok`). -/
theorem peek_any_races :
    (runSched peekP .any true "absent" [.a] [.c] 30 [.run .b, .run .a, .run .a]).store .a = some "a(absent)" ∧
    (runSched peekP .any true "absent" [.a] [.c] 30 [.run .a, .run .a, .run .a]).store .a = some "a(c(d))" := by
  decide +kernel

/-- **A peek that waits on the other forcer's hole agrees with the sequential answer** under every
schedule: `isCompleting` means "on this reader". -/
theorem peek_own_agrees :
    ∀ s ∈ scheds 6,
      let st := runSched peekP .own true "absent" [.a] [.c] 30 s
      st.idle = true ∧ st.answers = [.ok "a(c(d))", .ok "c(d)"] ∧ st.store .a = some "a(c(d))" := by
  decide +kernel

/-! ### Abort with a waiter

Both forcers demand `a` of the chain; the first takes it. Aborting the first after any number of
steps unwinds it; the second, waiting on `a`'s barrier (or on `b`'s, `c`'s, wherever the first
was), takes over. -/

/-- Every schedule of `k ≤ 6` steps beginning with the first forcer, then its abort. -/
def abortScheds : List (List Act) :=
  ((List.range 7).flatMap fun k => (scheds k).filter fun s => s.head? = some (.run .a)).map
    fun s => s ++ [.abort .a]

/-- **The waiter takes over.** With the hole released on unwinding, after every such schedule the
second forcer answers `a` as a run without the first would, and the store holds the chain. The
first forcer's work before the abort is kept (`abort_restart_ok`), and nothing it had in progress
is visible. -/
theorem abort_waiter_takes_over :
    ∀ s ∈ abortScheds,
      let st := runSched chainP .own true "absent" [.a] [.a] 30 s
      st.idle = true ∧ st.fb.results = [(.a, .ok "a(b(c(d)))")] ∧
        st.read [.a, .b, .c, .d] = [some "a(b(c(d)))", some "b(c(d))", some "c(d)", some "d"] := by
  decide +kernel

/-- **dotc's discipline leaves the waiter waiting.** With the hole kept on unwinding (`Touched`
never reset), the schedule that aborts the first forcer inside `a` leaves `a`'s hole owned by a
forcer that no longer exists; the second forcer waits on it for the rest of the run, and the
request is never answered. The sequential counterpart is `touched_stays_cyclic`: there the fact
was a cyclic reference, here it is a barrier nobody will release. -/
theorem abort_keep_hole_waiter_stuck :
    let st := runSched chainP .own false "absent" [.a] [.a] 30 [.run .a, .run .a, .run .b, .abort .a]
    st.idle = false ∧ st.fb.results = [] ∧ st.holes .a = some .a := by
  decide +kernel

end Query.Concurrent
