import Query.Lazy
import Query.Freeze
/-!
# Interrupting a lazy evaluator

A presentation compiler answers requests in the middle of a type check. "Interrupt" is two things:
**abort**, where the work in progress is thrown away and restarted (scalac's `FreshRunReq`,
IntelliJ's `ProcessCanceledException`), and **nested servicing**, where the request runs inside the
check in progress, on the same thread and symbol table (scalac's `signalDone` → `pollForWork`).
Over the lazy facts of `Query.Lazy` both are free, and this file says exactly how:

* **Abort** (§1). `forceA` is `force` with a budget of safepoints after which it stops and returns
  the store so far, and a `touched` set as the black hole instead of the stack, so that an aborted
  frame can leave it (scalac resets `LOCKED` in a `finally`) or stay (dotc's `Touched` is set in
  `completeFrom` and not reset when the completer throws). `forceA_agree`: every intermediate store
  agrees with the semantics, whatever the budget, and `abort_restart_ok`: restarting from it gives
  the same answers. `abort_touched` and `touched_stays_cyclic`: under dotc's discipline an aborted
  fact is a black hole for the rest of the run; `forceA_unlock_touched`: under scalac's it is not.
* **Nested servicing** (§2) with an empty stack is a reordering of demands
  (`nested_empty_stack_reorders`, from `forceAll_ok`). With a non-empty stack the request can
  black-hole on a fact that the program's own rules rank: a spurious cycle made by the interleaving
  (`nested_inside_frame_cycles`).
* **Peeking with taint** (§3). A consumer that peeks at a fact in progress (`Query.Lazy.forcePeek`)
  gets an answer that depends on the stack. `forceT` carries a taint: a result that saw `absent` is
  not memoized, as IntelliJ's `RecursionManager` forbids caching above the re-entered frame. Under
  ranked rules nothing ever peeks `absent` (`forcePeek_ok`), so the question only arises for a
  program with a cycle, and there full taint keeps the store in agreement with the fixed point
  (`forceT_agree`), where `forcePeek` memoizes an order-dependent answer
  (`forcePeek_memoizes_order`) and IntelliJ's rule, which does cache the re-entered frame, caches
  one too (`psi_root_order_dependent`).
* **State that is not a fact** (§4), the three shapes of scala/scala#11328: a member set grown in
  a burst and read at a safepoint inside it (`Query.Freeze` without the freeze), a map of synthetic
  trees consumed as they are added (a linear resource), and a cache of a symbol that a retype
  replaces (an identity cache).
-/

namespace Query.Interrupt

open Query.Lazy

variable {Q V : Type} [DecidableEq Q]

/-! ## 1. Abort: a forcing cut at a safepoint, and the two black-hole disciplines -/

/-- The outcome of an interruptible forcing: a value, a black hole, out of fuel, or aborted at a
safepoint. -/
inductive AOut (Q V : Type)
  | ok (v : V)
  | cyc (q : Q)
  | fuel
  | abort
  deriving DecidableEq, Repr

/-- The evaluator's state: the finished facts; the facts whose completer has been entered and not
left (scalac's `LOCKED`, dotc's `Touched`); and the safepoints left before the abort (`none`: no
abort is scheduled). -/
structure St (Q V : Type) where
  store : Store Q V
  touched : List Q
  budget : Option Nat

/-- A safepoint: the abort lands here if the budget is spent, else the budget ticks down. -/
def St.tick (st : St Q V) : Option (St Q V) :=
  match st.budget with
  | some 0 => none
  | some (b + 1) => some { st with budget := some b }
  | none => some st

omit [DecidableEq Q] in
theorem St.tick_eq {st st' : St Q V} (h : st.tick = some st') :
    st'.store = st.store ∧ st'.touched = st.touched := by
  unfold St.tick at h
  split at h <;> cases h <;> simp

/-- Run a task with a safepoint before each fact it asks (the toy's `signalDone` after each
member). -/
def runA (f : St Q V → Q → AOut Q V × St Q V) :
    Task Q (fun _ => V) V → St Q V → AOut Q V × St Q V
  | .pure v, st => (.ok v, st)
  | .ask q k, st =>
    match st.tick with
    | none => (.abort, st)
    | some st₁ =>
      match f st₁ q with
      | (.ok v, st') => runA f (k v) st'
      | (e, st') => (e, st')

/-- `force` with safepoints. Entering a completer marks the fact touched; leaving it with a value
stores the value and unmarks it; leaving it any other way (a black hole below, out of fuel, or the
abort) unmarks it only if `unlock` (scalac's `finally unlock()`; dotc leaves `Touched` set). -/
def forceA (R : Rules Q V) (unlock : Bool) : Nat → St Q V → Q → AOut Q V × St Q V
  | 0, st, _ => (.fuel, st)
  | n + 1, st, q =>
    match st.store q with
    | some v => (.ok v, st)
    | none =>
      if q ∈ st.touched then (.cyc q, st)
      else
        match runA (fun st' q' => forceA R unlock n st' q') (R q)
            { st with touched := q :: st.touched } with
        | (.ok v, st') =>
          (.ok v, { st' with store := upd st'.store q v, touched := st'.touched.erase q })
        | (e, st') => (e, if unlock then { st' with touched := st'.touched.erase q } else st')

omit [DecidableEq Q] in
/-- Running a task whose asked facts keep the store in agreement, with every value returned the
fact's value under `ρ`, keeps the store in agreement and returns the task's value under `ρ` when
it returns one, wherever the abort lands. -/
theorem runA_agree (ρ : Q → V) (f : St Q V → Q → AOut Q V × St Q V)
    (hf : ∀ st q, Agree ρ st.store →
      Agree ρ (f st q).2.store ∧ Ext st.store (f st q).2.store ∧
        ∀ v, (f st q).1 = .ok v → v = ρ q)
    (t : Task Q (fun _ => V) V) :
    ∀ st, Agree ρ st.store →
      Agree ρ (runA f t st).2.store ∧ Ext st.store (runA f t st).2.store ∧
        ∀ v, (runA f t st).1 = .ok v → v = t.run ρ := by
  induction t with
  | pure v =>
    intro st hs
    refine ⟨hs, Ext.refl _, fun v' h => ?_⟩
    simp only [runA, AOut.ok.injEq] at h
    exact h.symm
  | ask q k ih =>
    intro st hs
    cases ht : st.tick with
    | none =>
      simp only [runA, ht]
      exact ⟨hs, Ext.refl _, fun v h => by cases h⟩
    | some st₁ =>
      obtain ⟨h1, h2⟩ := St.tick_eq ht
      have hs₁ : Agree ρ st₁.store := h1 ▸ hs
      obtain ⟨a₁, e₁, v₁⟩ := hf st₁ q hs₁
      rcases hfq : f st₁ q with ⟨o, st'⟩
      rw [hfq] at a₁ e₁ v₁
      simp only at a₁ e₁ v₁
      cases o with
      | ok v =>
        have hv : v = ρ q := v₁ v rfl
        subst hv
        obtain ⟨a₂, e₂, v₂⟩ := ih (ρ q) st' a₁
        simp only [runA, ht, hfq]
        exact ⟨a₂, (h1 ▸ e₁ : Ext st.store st'.store).trans e₂, v₂⟩
      | cyc q' =>
        simp only [runA, ht, hfq]
        exact ⟨a₁, h1 ▸ e₁, fun v h => by cases h⟩
      | fuel =>
        simp only [runA, ht, hfq]
        exact ⟨a₁, h1 ▸ e₁, fun v h => by cases h⟩
      | abort =>
        simp only [runA, ht, hfq]
        exact ⟨a₁, h1 ▸ e₁, fun v h => by cases h⟩

/-- **Every prefix of a forcing is right as far as it goes.** With a fixed point `ρ` of the rules
(no ranking needed), forcing from a store that agrees with `ρ` leaves a store that agrees with `ρ`
and keeps every finished fact, whatever the budget, the fuel, the facts in progress and the
discipline; and a value returned is the fact's value under `ρ`. The stores a compiler leaves at
its safepoints are all consistent, so an abort anywhere loses work and nothing else. -/
theorem forceA_agree (R : Rules Q V) (unlock : Bool) (ρ : Q → V) (hfix : Fix R ρ) :
    ∀ n st q, Agree ρ st.store →
      Agree ρ (forceA R unlock n st q).2.store ∧ Ext st.store (forceA R unlock n st q).2.store ∧
        ∀ v, (forceA R unlock n st q).1 = .ok v → v = ρ q := by
  intro n
  induction n with
  | zero =>
    intro st q hs
    exact ⟨hs, Ext.refl _, fun v h => by cases h⟩
  | succ n ih =>
    intro st q hs
    cases hsq : st.store q with
    | some v =>
      simp only [forceA, hsq]
      exact ⟨hs, Ext.refl _, fun v' h => by injection h with h; exact h ▸ hs q v hsq⟩
    | none =>
      by_cases hin : q ∈ st.touched
      · simp only [forceA, hsq, hin, ↓reduceIte]
        exact ⟨hs, Ext.refl _, fun v h => by cases h⟩
      · have hrun := runA_agree ρ (fun st' q' => forceA R unlock n st' q')
          (fun st' q' hs' => ih st' q' hs') (R q) { st with touched := q :: st.touched } hs
        rcases hres : runA (fun st' q' => forceA R unlock n st' q') (R q)
          { st with touched := q :: st.touched } with ⟨o, st'⟩
        rw [hres] at hrun
        obtain ⟨a', e', v'⟩ := hrun
        simp only at a' e' v'
        simp only [forceA, hsq, hin, ↓reduceIte, hres]
        cases o with
        | ok v =>
          have hv : v = ρ q := by rw [v' v rfl, ← hfix q]
          refine ⟨?_, ?_, fun v'' h => by injection h with h; exact h ▸ hv⟩
          · intro x w hx
            simp only [upd] at hx
            split at hx
            · subst_vars; injection hx with hx; exact hx.symm
            · exact a' x w hx
          · intro x w hx
            simp only [upd]
            split
            · subst_vars; rw [hsq] at hx; cases hx
            · exact e' x w hx
        | cyc q' => cases unlock <;> exact ⟨a', e', fun v h => by cases h⟩
        | fuel => cases unlock <;> exact ⟨a', e', fun v h => by cases h⟩
        | abort => cases unlock <;> exact ⟨a', e', fun v h => by cases h⟩

/-- **Abort and restart gives the same answers.** With a ranked fixed point, a forcing cut at any
safepoint leaves a store from which forcing any fact (with fuel above its rank, and nothing in
progress) returns its value under `ρ`: the answer after a restart is the answer without the
interruption, and the work done before the abort is kept. scalac's `FreshRunReq` and IntelliJ's
`ProcessCanceledException` are sound over the facts. -/
theorem abort_restart_ok (R : Rules Q V) (unlock : Bool) (ρ : Q → V) (r : Q → Nat)
    (hfix : Fix R ρ) (hr : Ranked R ρ r) (n : Nat) (st : St Q V) (q : Q) (hs : Agree ρ st.store)
    (n' : Nat) (q' : Q) (hn' : r q' < n') :
    ∃ s', force R n' [] (forceA R unlock n st q).2.store q' = (.ok (ρ q'), s') ∧ Agree ρ s' ∧
      Ext (forceA R unlock n st q).2.store s' :=
  force_ok R ρ r hfix hr n' q' [] _ hn' (forceA_agree R unlock ρ hfix n st q hs).1 (by simp)

omit [DecidableEq Q] in
/-- A task's run never loses a touched fact: a frame unmarks only itself. -/
theorem runA_touched_mono (f : St Q V → Q → AOut Q V × St Q V)
    (hf : ∀ st q, ∀ x ∈ st.touched, x ∈ (f st q).2.touched) (t : Task Q (fun _ => V) V) :
    ∀ st, ∀ x ∈ st.touched, x ∈ (runA f t st).2.touched := by
  induction t with
  | pure v => intro st x hx; exact hx
  | ask q k ih =>
    intro st x hx
    cases ht : st.tick with
    | none => simpa [runA, ht] using hx
    | some st₁ =>
      obtain ⟨_, h2⟩ := St.tick_eq ht
      have hx₁ : x ∈ st₁.touched := h2 ▸ hx
      have := hf st₁ q x hx₁
      rcases hfq : f st₁ q with ⟨o, st'⟩
      rw [hfq] at this
      cases o <;> simp only [runA, ht, hfq]
      · exact ih _ st' x this
      all_goals exact this

/-- A forcing never loses a touched fact either, under either discipline. -/
theorem forceA_touched_mono (R : Rules Q V) (unlock : Bool) :
    ∀ n st q, ∀ x ∈ st.touched, x ∈ (forceA R unlock n st q).2.touched := by
  intro n
  induction n with
  | zero => intro st q x hx; exact hx
  | succ n ih =>
    intro st q x hx
    cases hsq : st.store q with
    | some v => simpa [forceA, hsq] using hx
    | none =>
      by_cases hin : q ∈ st.touched
      · simpa [forceA, hsq, hin] using hx
      · have hmono := runA_touched_mono (fun st' q' => forceA R unlock n st' q')
          (fun st' q' => ih st' q') (R q) { st with touched := q :: st.touched } x
          (by simp [hx])
        have hne : x ≠ q := fun h => hin (h ▸ hx)
        rcases hres : runA (fun st' q' => forceA R unlock n st' q') (R q)
          { st with touched := q :: st.touched } with ⟨o, st'⟩
        rw [hres] at hmono
        simp only [forceA, hsq, hin, ↓reduceIte, hres]
        cases o with
        | ok v => exact (List.mem_erase_of_ne hne).2 hmono
        | cyc q' => cases unlock <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            first | exact hmono | exact (List.mem_erase_of_ne hne).2 hmono
        | fuel => cases unlock <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            first | exact hmono | exact (List.mem_erase_of_ne hne).2 hmono
        | abort => cases unlock <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            first | exact hmono | exact (List.mem_erase_of_ne hne).2 hmono

/-- **dotc's discipline: an aborted fact stays touched.** Without `unlock`, a forcing of `q` that
is aborted leaves `q` in the touched set (and every frame below it, by the same argument), since
only a frame that returns a value unmarks itself. -/
theorem abort_touched (R : Rules Q V) (n : Nat) (st : St Q V) (q : Q)
    (hsq : st.store q = none) (hin : q ∉ st.touched)
    (h : (forceA R false (n + 1) st q).1 = .abort) :
    q ∈ (forceA R false (n + 1) st q).2.touched := by
  have hmono := runA_touched_mono (fun st' q' => forceA R false n st' q')
    (fun st' q' => forceA_touched_mono R false n st' q') (R q)
    { st with touched := q :: st.touched } q (by simp)
  rcases hres : runA (fun st' q' => forceA R false n st' q') (R q)
    { st with touched := q :: st.touched } with ⟨o, st'⟩
  rw [hres] at hmono
  simp only [forceA, hsq, hin, ↓reduceIte, hres] at h ⊢
  cases o <;> simp_all

/-- **A touched fact is a black hole**: forcing it, from any state in which it is touched and not
finished, is a cyclic reference. With `abort_touched`, under dotc's discipline an aborted fact is
a cyclic reference for the rest of the run (the hypothetical `dotc-interrupted` kernel of the toy;
dotc under Metals avoids it by never interrupting and by throwing the driver away on any other
exception). -/
theorem touched_stays_cyclic (R : Rules Q V) (unlock : Bool) (n : Nat) (st : St Q V) (q : Q)
    (hsq : st.store q = none) (hin : q ∈ st.touched) :
    forceA R unlock (n + 1) st q = (.cyc q, st) := by
  simp [forceA, hsq, hin]

omit [DecidableEq Q] in
/-- A task's run under scalac's discipline leaves the touched set as it found it. -/
theorem runA_touched_eq (f : St Q V → Q → AOut Q V × St Q V)
    (hf : ∀ st q, (f st q).2.touched = st.touched) (t : Task Q (fun _ => V) V) :
    ∀ st, (runA f t st).2.touched = st.touched := by
  induction t with
  | pure v => intro st; rfl
  | ask q k ih =>
    intro st
    cases ht : st.tick with
    | none => simp [runA, ht]
    | some st₁ =>
      obtain ⟨_, h2⟩ := St.tick_eq ht
      have := hf st₁ q
      rcases hfq : f st₁ q with ⟨o, st'⟩
      rw [hfq] at this
      cases o <;> simp only [runA, ht, hfq]
      · rw [ih _ st', this, h2]
      all_goals rw [this, h2]

/-- **scalac's discipline: an aborted frame leaves the stack.** With `unlock`, every forcing,
however it ends, leaves the touched set as it found it: after an abort unwinds to the top nothing
is touched, and the restart of `abort_restart_ok` finds no black hole. -/
theorem forceA_unlock_touched (R : Rules Q V) :
    ∀ n st q, (forceA R true n st q).2.touched = st.touched := by
  intro n
  induction n with
  | zero => intro st q; rfl
  | succ n ih =>
    intro st q
    cases hsq : st.store q with
    | some v => simp [forceA, hsq]
    | none =>
      by_cases hin : q ∈ st.touched
      · simp [forceA, hsq, hin]
      · have heq := runA_touched_eq (fun st' q' => forceA R true n st' q')
          (fun st' q' => ih st' q') (R q) { st with touched := q :: st.touched }
        rcases hres : runA (fun st' q' => forceA R true n st' q') (R q)
          { st with touched := q :: st.touched } with ⟨o, st'⟩
        rw [hres] at heq
        simp only at heq
        simp only [forceA, hsq, hin, ↓reduceIte, hres]
        cases o <;> simp [heq]

/-! ### The two disciplines on a chain

`a` asks `b`, `b` asks `c`, `c` asks `d`. A budget of two safepoints aborts inside `c`'s
completer. -/

inductive Chain | a | b | c | d
  deriving DecidableEq, Repr

def chain : Rules Chain String
  | .a => .ask .b fun v => .pure s!"a({v})"
  | .b => .ask .c fun v => .pure s!"b({v})"
  | .c => .ask .d fun v => .pure s!"c({v})"
  | .d => .pure "d"

/-- The empty state with `k` safepoints before the abort. -/
def fresh (k : Option Nat) : St Chain String := ⟨fun _ => none, [], k⟩

/-- The abort lands inside `c`; scalac's discipline leaves nothing touched, dotc's leaves the
three frames. -/
theorem chain_abort_scalac : (forceA chain true 9 (fresh (some 2)) .a).1 = .abort ∧
    (forceA chain true 9 (fresh (some 2)) .a).2.touched = [] := by decide

theorem chain_abort_dotc : (forceA chain false 9 (fresh (some 2)) .a).1 = .abort ∧
    (forceA chain false 9 (fresh (some 2)) .a).2.touched = [.c, .b, .a] := by decide

/-- Restarting from the aborted state: scalac's run answers, dotc's black-holes at `a`. -/
theorem chain_restart_scalac :
    (forceA chain true 9 { (forceA chain true 9 (fresh (some 2)) .a).2 with budget := none } .a).1 =
      .ok "a(b(c(d)))" := by decide

theorem chain_restart_dotc :
    (forceA chain false 9 { (forceA chain false 9 (fresh (some 2)) .a).2 with budget := none } .a).1 =
      .cyc .a := by decide

/-! ## 2. Nested servicing: a reordering, or a spurious cycle -/

/-- **A request serviced with an empty stack is a reordering of demands.** The background has
forced `before` and will force `after`; the request `req` is serviced in between, at a safepoint
with nothing in progress. With a ranked fixed point every answer, the request's and the
background's, is the value under `ρ`, the same as with the request serviced after the background
(`forceAll_ok` for both sequences). scalac's `pollForWork` at `signalDone` with `lockedCount == 0`
is this. -/
theorem nested_empty_stack_reorders (R : Rules Q V) (ρ : Q → V) (r : Q → Nat)
    (hfix : Fix R ρ) (hr : Ranked R ρ r) (n : Nat) (before req after : List Q)
    (hn : ∀ q ∈ before ++ req ++ after, r q < n) (s : Store Q V) (hs : Agree ρ s) :
    (forceAll R n (before ++ req ++ after) s).1 = (before ++ req ++ after).map (fun q => .ok (ρ q)) ∧
    (forceAll R n (before ++ after ++ req) s).1 = (before ++ after ++ req).map (fun q => .ok (ρ q)) :=
  ⟨forceAll_ok R ρ r hfix hr n _ hn s hs,
   forceAll_ok R ρ r hfix hr n _
    (fun q (hq : q ∈ before ++ after ++ req) => hn q (by
      simp only [List.mem_append] at hq ⊢
      rcases hq with (h | h) | h <;> simp [h])) s hs⟩

/-! ### With a frame in progress: a spurious cycle

`a` asks `b`; `c` asks `a`. Ranked (`b`, `a`, `c`), so alone every demand answers. A request for
`c` serviced at the safepoint inside `a`'s completer, after `b` has returned, finds `a` in
progress: a cyclic reference that no order of top-level demands produces. This is why scalac
services nothing while `lockedCount > 0`, and why the toy's `signalDone` inside a completer is
not a servicing point. -/

inductive N3 | a | b | c
  deriving DecidableEq, Repr

def nested3 : Rules N3 String
  | .a => .ask .b fun v => .pure s!"a({v})"
  | .b => .pure "b"
  | .c => .ask .a fun v => .pure s!"c({v})"

theorem nested3_ranked :
    Ranked nested3 (fun q => (nested3 q).run fun | .a => "a(b)" | .b => "b" | .c => "c(a(b))")
      fun | .b => 0 | .a => 1 | .c => 2 := by
  intro q q' h; cases q <;> simp [nested3, Task.trace] at h <;> subst h <;> decide

/-- Serviced with nothing in progress, `c` answers. -/
theorem nested3_empty_stack_ok :
    (force nested3 5 [] (fun _ => none) .c).1 = .ok "c(a(b))" := by decide

/-- Serviced inside `a`'s completer (the stack `[a]`, `b` already stored), `c` black-holes. -/
theorem nested_inside_frame_cycles :
    (force nested3 5 [.a] (fun q => if q = .b then some "b" else none) .c).1 = .cyc .a := by
  decide

/-! ## 3. Peeking with taint -/

/-- The fact a probe is about. -/
def fact : Probe Q → Q
  | .force q => q
  | .peek q => q

/-- The semantics of peeking rules reads a peek as a force: the value the fact has once finished. -/
def probeEnv (ρ : Q → V) : Probe Q → V := fun p => ρ (fact p)

/-- `ρ` is a fixed point of peeking rules, with every peek read as a force. -/
def PFix (R : PRules Q V) (ρ : Q → V) : Prop := ∀ q, ρ q = (R q).run (probeEnv ρ)

/-- A rank that decreases along every fact a peeking rule asks or peeks under `ρ`. -/
def PRanked (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) : Prop :=
  ∀ q, ∀ p ∈ (R q).trace (probeEnv ρ), r (fact p) < r q

/-- `runPeek` over a task none of whose probes finds its fact in progress, where every force
returns the fact's value: the task's value under `ρ`. -/
theorem runPeek_ok (ρ : Q → V) (stk : List Q) (absent : V)
    (f : Store Q V → Q → Out Q V × Store Q V) (t : Task (Probe Q) (fun _ => V) V)
    (hf : ∀ p ∈ t.trace (probeEnv ρ), (fact p) ∉ stk ∧ ∀ s, Agree ρ s →
      ∃ s', f s (fact p) = (.ok (ρ (fact p)), s') ∧ Agree ρ s' ∧ Ext s s') :
    ∀ s, Agree ρ s →
      ∃ s', runPeek stk absent f t s = (.ok (t.run (probeEnv ρ)), s') ∧ Agree ρ s' ∧ Ext s s' := by
  induction t with
  | pure v => intro s hs; exact ⟨s, rfl, hs, Ext.refl s⟩
  | ask p k ih =>
    intro s hs
    obtain ⟨hnot, hp⟩ := hf p (by simp [Task.trace])
    obtain ⟨s₁, h₁, a₁, e₁⟩ := hp s hs
    have hk : ∀ p' ∈ (k (probeEnv ρ p)).trace (probeEnv ρ), (fact p') ∉ stk ∧ ∀ s, Agree ρ s →
        ∃ s', f s (fact p') = (.ok (ρ (fact p')), s') ∧ Agree ρ s' ∧ Ext s s' :=
      fun p' hp' => hf p' (by simp [Task.trace, hp'])
    obtain ⟨s₂, h₂, a₂, e₂⟩ := ih (probeEnv ρ p) hk s₁ a₁
    refine ⟨s₂, ?_, a₂, e₁.trans e₂⟩
    cases p with
    | force q => simp only [runPeek, fact] at h₁ ⊢; rw [h₁]; exact h₂
    | peek q =>
      simp only [fact] at hnot h₁
      simp only [runPeek, hnot, ↓reduceIte, h₁]
      exact h₂

/-- **Under ranked rules nothing peeks `absent`.** With a ranked fixed point, `forcePeek` from a
consistent store returns the fact's value, never black-holes, and every peek finds its fact not in
progress: taint has nothing to do, and the store agrees with `ρ`. The order dependence of a
peeking consumer (`ScalaTypes.Laziness.implicitSkip_*`) is confined to programs whose definitions,
with the peek read as a force, are cyclic. -/
theorem forcePeek_ok (R : PRules Q V) (ρ : Q → V) (r : Q → Nat) (absent : V)
    (hfix : PFix R ρ) (hr : PRanked R ρ r) :
    ∀ n q stk s, r q < n → Agree ρ s → (∀ x ∈ stk, r q < r x) →
      ∃ s', forcePeek R absent n stk s q = (.ok (ρ q), s') ∧ Agree ρ s' ∧ Ext s s' := by
  intro n
  induction n with
  | zero => intro q _ _ h; omega
  | succ n ih =>
    intro q stk s hn hs hstk
    cases hsq : s q with
    | some v =>
      refine ⟨s, ?_, hs, Ext.refl s⟩
      simp only [forcePeek, hsq]
      rw [hs q v hsq]
    | none =>
      have hnot : q ∉ stk := fun hm => by have := hstk q hm; omega
      have hf : ∀ p ∈ (R q).trace (probeEnv ρ), fact p ∉ q :: stk ∧ ∀ s, Agree ρ s →
          ∃ s', forcePeek R absent n (q :: stk) s (fact p) = (.ok (ρ (fact p)), s') ∧
            Agree ρ s' ∧ Ext s s' := by
        intro p hp
        have hlt := hr q p hp
        refine ⟨?_, fun s' hs' => ih (fact p) (q :: stk) s' (by omega) hs' ?_⟩
        · intro hx
          simp only [List.mem_cons] at hx
          rcases hx with hx | hx
          · rw [hx] at hlt; omega
          · have := hstk (fact p) hx; omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hlt
          · have := hstk x hx; omega
      have hrun := runPeek_ok ρ (q :: stk) absent
        (fun s' q' => forcePeek R absent n (q :: stk) s' q') (R q) hf s hs
      obtain ⟨s', h', a', e'⟩ := hrun
      refine ⟨upd s' q (ρ q), ?_, ?_, ?_⟩
      · simp only [forcePeek, hsq, hnot, ↓reduceIte, h']
        rw [← hfix q]
      · intro x v hx
        simp only [upd] at hx
        split at hx
        · subst_vars; injection hx with hx; exact hx.symm
        · exact a' x v hx
      · intro x v hx
        simp only [upd]
        split
        · subst_vars; rw [hsq] at hx; cases hx
        · exact e' x v hx

/-! ### The taint

A result's taint says which frames may still cache it: `none`, every frame; `some m`, only the
frames below position `m` on the stack (the bottom frame is position 0). A peek that finds its
fact in progress at position `p` taints the frames strictly above it (`some (p + 1)`), which is
IntelliJ's `RecursionManager.prohibitResultCaching`; or, in full mode, every frame (`some 0`). -/

abbrev Taint := Option Nat

def Taint.join : Taint → Taint → Taint
  | none, t => t
  | t, none => t
  | some m, some m' => some (min m m')

/-- May a frame at position `d` cache a result with this taint? In full mode a tainted result is
never cached. -/
def Taint.caches (psi : Bool) : Taint → Nat → Bool
  | none, _ => true
  | some m, d => psi && decide (d < m)

/-- The position above which a peek at `q`, in progress on `stk` (top first), taints: in IntelliJ's
mode the frames strictly above `q`'s; in full mode all of them. -/
def reentry (psi : Bool) (stk : List Q) (q : Q) : Taint :=
  some (if psi then stk.length - stk.idxOf q else 0)

theorem Taint.join_eq_none {t t' : Taint} (h : t.join t' = none) : t = none ∧ t' = none := by
  cases t <;> cases t' <;> simp_all [Taint.join]

theorem Taint.join_some_ne_none (t : Taint) (m : Nat) : t.join (some m) ≠ none := by
  cases t <;> simp [Taint.join]

/-- Run a peeking task, carrying the taint: a peek at a fact in progress answers `absent` and
taints the frames above it; a value from a nested forcing brings its taint along. -/
def runT (psi : Bool) (stk : List Q) (absent : V)
    (f : Store Q V → Q → Out Q V × Store Q V × Taint) :
    Task (Probe Q) (fun _ => V) V → Store Q V → Out Q V × Store Q V × Taint
  | .pure v, s => (.ok v, s, none)
  | .ask (.peek q) k, s =>
    if q ∈ stk then
      match runT psi stk absent f (k absent) s with
      | (o, s', t) => (o, s', t.join (reentry psi stk q))
    else match f s q with
      | (.ok v, s', t) =>
        match runT psi stk absent f (k v) s' with
        | (o, s'', t') => (o, s'', t.join t')
      | (e, s', t) => (e, s', t)
  | .ask (.force q) k, s =>
    match f s q with
    | (.ok v, s', t) =>
      match runT psi stk absent f (k v) s' with
      | (o, s'', t') => (o, s'', t.join t')
    | (e, s', t) => (e, s', t)

/-- `forcePeek` with taint: a value is stored only if its taint lets the frame cache it. With
`psi`, IntelliJ's rule (the re-entered frame caches, the frames above it do not); without,
full taint (nothing computed from an `absent` is cached). -/
def forceT (R : PRules Q V) (psi : Bool) (absent : V) :
    Nat → List Q → Store Q V → Q → Out Q V × Store Q V × Taint
  | 0, _, s, _ => (.fuel, s, none)
  | n + 1, stk, s, q =>
    match s q with
    | some v => (.ok v, s, none)
    | none =>
      if q ∈ stk then (.cyc q, s, none)
      else
        match runT psi (q :: stk) absent (fun s' q' => forceT R psi absent n (q :: stk) s' q') (R q) s with
        | (.ok v, s', t) => (.ok v, if t.caches psi stk.length then upd s' q v else s', t)
        | (e, s', t) => (e, s', t)

def forceTAll (R : PRules Q V) (psi : Bool) (absent : V) (n : Nat) :
    List Q → Store Q V → List (Out Q V) × Store Q V
  | [], s => ([], s)
  | q :: qs, s =>
    match forceT R psi absent n [] s q with
    | (o, s₁, _) =>
      match forceTAll R psi absent n qs s₁ with
      | (os, s₂) => (o :: os, s₂)

/-- Running a task in full taint mode, with nested forcings that keep the store in agreement and
whose untainted values are the facts' values: the store stays in agreement, and an untainted
result is the task's value under `ρ`. -/
theorem runT_agree (ρ : Q → V) (stk : List Q) (absent : V)
    (f : Store Q V → Q → Out Q V × Store Q V × Taint)
    (hf : ∀ s q, Agree ρ s → Agree ρ (f s q).2.1 ∧ Ext s (f s q).2.1 ∧
      ∀ v, (f s q).1 = .ok v → (f s q).2.2 = none → v = ρ q)
    (t : Task (Probe Q) (fun _ => V) V) :
    ∀ s, Agree ρ s →
      Agree ρ (runT false stk absent f t s).2.1 ∧ Ext s (runT false stk absent f t s).2.1 ∧
        ∀ v, (runT false stk absent f t s).1 = .ok v → (runT false stk absent f t s).2.2 = none →
          v = t.run (probeEnv ρ) := by
  induction t with
  | pure v =>
    intro s hs
    refine ⟨hs, Ext.refl _, fun v' h _ => ?_⟩
    simp only [runT, Out.ok.injEq] at h
    exact h.symm
  | ask p k ih =>
    intro s hs
    -- the forcing branch, shared by `force q` and a `peek q` with `q` not in progress
    have forced : ∀ q, (p = .force q ∨ (p = .peek q ∧ q ∉ stk)) →
        Agree ρ (runT false stk absent f (.ask p k) s).2.1 ∧
        Ext s (runT false stk absent f (.ask p k) s).2.1 ∧
        ∀ v, (runT false stk absent f (.ask p k) s).1 = .ok v →
          (runT false stk absent f (.ask p k) s).2.2 = none → v = (Task.ask p k).run (probeEnv ρ) := by
      intro q hpq
      obtain ⟨a₁, e₁, v₁⟩ := hf s q hs
      rcases hfq : f s q with ⟨o, s', t⟩
      rw [hfq] at a₁ e₁ v₁
      simp only at a₁ e₁ v₁
      have unfold : runT false stk absent f (.ask p k) s =
          match (o, s', t) with
          | (.ok v, s', t) =>
            match runT false stk absent f (k v) s' with
            | (o, s'', t') => (o, s'', t.join t')
          | (e, s', t) => (e, s', t) := by
        rcases hpq with rfl | ⟨rfl, hnot⟩
        · simp only [runT, hfq]
        · simp only [runT, hnot, ↓reduceIte, hfq]
      rw [unfold]
      cases o with
      | ok v =>
        obtain ⟨a₂, e₂, v₂⟩ := ih v s' a₁
        rcases hrun : runT false stk absent f (k v) s' with ⟨o₂, s₂, t₂⟩
        rw [hrun] at a₂ e₂ v₂
        simp only at a₂ e₂ v₂
        simp only [hrun]
        refine ⟨a₂, e₁.trans e₂, fun v' ho ht => ?_⟩
        obtain ⟨ht₁, ht₂⟩ := Taint.join_eq_none ht
        have hv : v = ρ q := v₁ v rfl ht₁
        have hp : probeEnv ρ p = ρ q := by
          rcases hpq with rfl | ⟨rfl, _⟩ <;> rfl
        rw [Task.run_ask, hp, ← hv]
        exact v₂ v' ho ht₂
      | cyc q' => exact ⟨a₁, e₁, fun v h => by cases h⟩
      | fuel => exact ⟨a₁, e₁, fun v h => by cases h⟩
    cases p with
    | force q => exact forced q (Or.inl rfl)
    | peek q =>
      by_cases hin : q ∈ stk
      · obtain ⟨a₂, e₂, _⟩ := ih absent s hs
        rcases hrun : runT false stk absent f (k absent) s with ⟨o₂, s₂, t₂⟩
        rw [hrun] at a₂ e₂
        simp only at a₂ e₂
        simp only [runT, hin, ↓reduceIte, hrun]
        exact ⟨a₂, e₂, fun v _ ht => absurd ht (Taint.join_some_ne_none _ _)⟩
      · exact forced q (Or.inr ⟨rfl, hin⟩)

/-- **Full taint keeps the store in agreement with the fixed point**, for any program that has
one, cyclic or not: nothing computed from an `absent` is memoized, so every stored value is the
fact's value with every peeked fact finished. A fact in a cycle through a peek is recomputed on
every demand and never stored; the price IntelliJ accepts for cached values that are pure
functions of the sources. -/
theorem forceT_agree (R : PRules Q V) (absent : V) (ρ : Q → V) (hfix : PFix R ρ) :
    ∀ n stk s q, Agree ρ s →
      Agree ρ (forceT R false absent n stk s q).2.1 ∧ Ext s (forceT R false absent n stk s q).2.1 ∧
        ∀ v, (forceT R false absent n stk s q).1 = .ok v →
          (forceT R false absent n stk s q).2.2 = none → v = ρ q := by
  intro n
  induction n with
  | zero => intro stk s q hs; exact ⟨hs, Ext.refl _, fun v h => by cases h⟩
  | succ n ih =>
    intro stk s q hs
    cases hsq : s q with
    | some v =>
      simp only [forceT, hsq]
      exact ⟨hs, Ext.refl _, fun v' h _ => by injection h with h; exact h ▸ hs q v hsq⟩
    | none =>
      by_cases hin : q ∈ stk
      · simp only [forceT, hsq, hin, ↓reduceIte]
        exact ⟨hs, Ext.refl _, fun v h => by cases h⟩
      · have hf : ∀ s' q', Agree ρ s' →
            Agree ρ (forceT R false absent n (q :: stk) s' q').2.1 ∧
            Ext s' (forceT R false absent n (q :: stk) s' q').2.1 ∧
            ∀ v, (forceT R false absent n (q :: stk) s' q').1 = .ok v →
              (forceT R false absent n (q :: stk) s' q').2.2 = none → v = ρ q' :=
          fun s' q' hs' => ih (q :: stk) s' q' hs'
        have hrun := runT_agree ρ (q :: stk) absent
          (fun s' q' => forceT R false absent n (q :: stk) s' q') hf (R q) s hs
        rcases hres : runT false (q :: stk) absent (fun s' q' => forceT R false absent n (q :: stk) s' q')
          (R q) s with ⟨o, s', t⟩
        rw [hres] at hrun
        obtain ⟨a', e', v'⟩ := hrun
        simp only at a' e' v'
        simp only [forceT, hsq, hin, ↓reduceIte, hres]
        cases o with
        | ok v =>
          cases t with
          | none =>
            have hv : v = ρ q := by rw [v' v rfl rfl, ← hfix q]
            simp only [Taint.caches, ↓reduceIte]
            refine ⟨?_, ?_, fun v'' h _ => by injection h with h; exact h ▸ hv⟩
            · intro x w hx
              simp only [upd] at hx
              split at hx
              · subst_vars; injection hx with hx; exact hx.symm
              · exact a' x w hx
            · intro x w hx
              simp only [upd]
              split
              · subst_vars; rw [hsq] at hx; cases hx
              · exact e' x w hx
          | some m =>
            simp only [Taint.caches, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact ⟨a', e', fun v'' _ h => by cases h⟩
        | cyc q' => exact ⟨a', e', fun v h => by cases h⟩
        | fuel => exact ⟨a', e', fun v h => by cases h⟩

/-! ### Two facts that peek at each other

`a` peeks `b`, `b` peeks `a`; each answers with what it saw. No fixed point exists (each value
would contain the other), so the question is only what gets memoized. -/

inductive P2 | a | b
  deriving DecidableEq, Repr

def peekBoth : PRules P2 String
  | .a => .ask (.peek .b) fun v => .pure s!"a({v})"
  | .b => .ask (.peek .a) fun v => .pure s!"b({v})"

/-- **`forcePeek` memoizes an order-dependent answer**: demanded `a` then `b`, the store holds
`b = b(absent)`; demanded `b` then `a`, it holds `b = b(a(absent))`. Two orders, two stored values
of the same fact (scalac's implicit search over a `LOCKED` candidate, memoized in the symbol's
info). -/
theorem forcePeek_memoizes_order :
    (forcePeekAll peekBoth "absent" 5 [.a, .b] (fun _ => none)).2 .b = some "b(absent)" ∧
    (forcePeekAll peekBoth "absent" 5 [.b, .a] (fun _ => none)).2 .b = some "b(a(absent))" := by
  decide

/-- **IntelliJ's rule caches the re-entered frame**, whose value was computed with `null` for its
own re-entry: `a` demanded first is stored as `a(b(absent))`, `b` first stores `b(a(absent))` and
then `a` as `a(b(a(absent)))`. The frames above the re-entered one are not cached, but the root
of the cycle is, and which fact is the root is the demand order. -/
theorem psi_root_order_dependent :
    (forceTAll peekBoth true "absent" 5 [.a, .b] (fun _ => none)).2 .a = some "a(b(absent))" ∧
    (forceTAll peekBoth true "absent" 5 [.b, .a] (fun _ => none)).2 .a = some "a(b(a(absent)))" := by
  decide

/-- **Full taint stores nothing on the cycle**, in either order: the answers still depend on who
asks, but no answer is remembered, so no later consumer inherits the order. -/
theorem fullTaint_stores_nothing :
    (forceTAll peekBoth false "absent" 5 [.a, .b] (fun _ => none)).2 .a = none ∧
    (forceTAll peekBoth false "absent" 5 [.a, .b] (fun _ => none)).2 .b = none ∧
    (forceTAll peekBoth false "absent" 5 [.b, .a] (fun _ => none)).2 .a = none ∧
    (forceTAll peekBoth false "absent" 5 [.b, .a] (fun _ => none)).2 .b = none := by
  decide

/-! ## 4. The state that is not a fact

The three shapes of scala/scala#11328, each the mutable state and the invariant it needs at a
safepoint. The fourth, a completeness claim made by a computation that stopped early
(`suppressionsKnown`), is the first shape again with the set of `@nowarn`s as the burst. -/

/-! ### (a) A fact grown in a burst, read at a safepoint inside it

`addSyntheticMethods` enters `copy`, `equals`, `hashCode` and `toString` into a case class's
members one at a time, with a safepoint after each. A request serviced at the `k`th safepoint
retypes the class: it reads the member set as pushed so far (`Query.Freeze.unguarded` with the
read at `k`), and adds what its policy says. All-or-nothing (scalac's "already has … not adding"):
if anything is there, add nothing. Per element (the proposal `idempotentSynthetics`): add what is
missing. The request's view is what it read plus what it added. -/

/-- The burst's pushes with the read at safepoint `k`, in push order. -/
def readAt {C : Type} (burst : List C) (k : Nat) : List C :=
  ((Query.Freeze.unguarded ((burst.take k).map .push ++ [.read] ++ (burst.drop k).map .push) []).headD []).reverse

def allOrNothing {C : Type} (burst seen : List C) : List C := if seen.isEmpty then burst else []

def perElement {C : Type} [DecidableEq C] (burst seen : List C) : List C := burst.filter (· ∉ seen)

/-- The view of a request serviced at safepoint `k`. -/
def viewAt {C : Type} (policy : List C → List C → List C) (burst : List C) (k : Nat) : List C :=
  readAt burst k ++ policy burst (readAt burst k)

def whole {C : Type} [DecidableEq C] (burst view : List C) : Bool :=
  burst.all (· ∈ view) && view.length == burst.length

def synthetics : List String := ["copy", "equals", "hashCode", "toString"]

/-- **All-or-nothing is whole only outside the burst**: at the safepoints inside it the request
sees a prefix and adds nothing. "Uninterruptible" (`uninterruptible(addSyntheticMethods)`) is the
burst having only safepoints 0 and 4. -/
theorem burst_allOrNothing_whole_iff :
    ∀ k, k ≤ 4 → (whole synthetics (viewAt allOrNothing synthetics k) ↔ k = 0 ∨ k = 4) := by
  decide

/-- **Per element is whole at every safepoint**: the request adds what it did not see. -/
theorem burst_perElement_whole :
    ∀ k, k ≤ 4 → whole synthetics (viewAt perElement synthetics k) = true := by
  decide

/-! ### (b) A consumed map: a linear resource

`unit.synthetics` holds the trees a case class's companion gets (`apply`, `unapply`, and the
companion itself); `addSynthetics` moves each into the tree being typed and removes it from the
map. Two checks of the same template, interleaved at safepoints (a targeted request inside the
background check, or a nested `askType`), each walk the map. A consuming add gives each item to
the check that reaches it first; an idempotent add (the PR's `SynthesizedMethods` attachment, in
effect) gives it to both. -/

/-- Every interleaving of two sequences (with a fuel, so that `decide` can run it). -/
def mergesF {α : Type} : Nat → List α → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, [], ys => [ys]
  | _ + 1, x :: xs, [] => [x :: xs]
  | n + 1, x :: xs, y :: ys =>
    (mergesF n xs (y :: ys)).map (x :: ·) ++ (mergesF n (x :: xs) ys).map (y :: ·)

def merges {α : Type} (xs ys : List α) : List (List α) := mergesF (xs.length + ys.length + 1) xs ys

/-- The two checks' trees and the map, after a list of steps `(check, item)`. -/
def addAll {I : Type} [DecidableEq I] (consuming : Bool) :
    List (Bool × I) → List I → List I → List I → List I × List I
  | [], _, ta, tb => (ta, tb)
  | (c, i) :: steps, pool, ta, tb =>
    if i ∈ pool then
      addAll consuming steps (if consuming then pool.erase i else pool)
        (if c then ta ++ [i] else ta) (if c then tb else tb ++ [i])
    else addAll consuming steps pool ta tb

def items : List String := ["companion", "apply", "unapply"]

def steps (c : Bool) : List (Bool × String) := items.map (c, ·)

/-- **An idempotent add gives both trees every item, under every interleaving.** -/
theorem idempotent_add_complete :
    ∀ il ∈ merges (steps true) (steps false),
      (addAll false il items [] []).1 = items ∧ (addAll false il items [] []).2 = items := by
  decide

/-- **A consuming add gives each item to exactly one tree**, under every interleaving: the other
tree, which may be the one that is kept (the background's, assigned last by `typeCheck`), lacks
it. -/
theorem consuming_add_one_owner :
    ∀ il ∈ merges (steps true) (steps false), ∀ i ∈ items,
      (i ∈ (addAll true il items [] []).1) ≠ (i ∈ (addAll true il items [] []).2) := by
  decide

/-! ### (c) An identity cache

scalac's implicit search caches the implicits in scope for the run (`implicitss`), and skips a
cached candidate the name no longer resolves to ("shadowed"). The factory method of an implicit
class is entered each time its template is typed (`enterImplicitWrapper`): before the PR, a new
symbol replacing the old; after it, the same symbol. The cache holds a symbol by identity, so it
is sound only if that identity is stable within the run. -/

inductive CEv | retype | lookup
  deriving DecidableEq, Repr

structure CSt where
  current : Nat
  cache : Option Nat
  found : List Bool

/-- A retype replaces the symbol (`keep = false`) or keeps it; a lookup fills the cache on first
use and then answers whether the cached symbol is the current one. -/
def cacheStep (keep : Bool) (st : CSt) : CEv → CSt
  | .retype => if keep then st else { st with current := st.current + 1 }
  | .lookup =>
    match st.cache with
    | none => { st with cache := some st.current, found := true :: st.found }
    | some c => { st with found := (c == st.current) :: st.found }

def cacheRun (keep : Bool) : List CEv → CSt → CSt
  | [], st => st
  | e :: es, st => cacheRun keep es (cacheStep keep st e)

/-- **A kept symbol makes the cache sound**: every lookup, under every schedule of retypes and
lookups, finds the implicit. -/
theorem keep_cache_sound (evs : List CEv) (st : CSt)
    (h : st.cache = none ∨ st.cache = some st.current) (hf : ∀ b ∈ st.found, b = true) :
    ∀ b ∈ (cacheRun true evs st).found, b = true := by
  induction evs generalizing st with
  | nil => exact hf
  | cons e es ih =>
    cases e with
    | retype => exact ih st h hf
    | lookup =>
      rcases h with h | h
      · apply ih
        · simp [cacheStep, h]
        · intro b hb
          simp only [cacheStep, h, List.mem_cons] at hb
          rcases hb with rfl | hb
          · rfl
          · exact hf b hb
      · apply ih
        · simp [cacheStep, h]
        · intro b hb
          simp only [cacheStep, h, List.mem_cons, beq_self_eq_true] at hb
          rcases hb with rfl | hb
          · rfl
          · exact hf b hb

/-- **A replaced symbol makes it unsound**: a lookup fills the cache, a retype replaces the
factory, the next lookup finds the cached symbol shadowed. The `implicit-class` scenario's
divergent safepoints are exactly the ones between a fill and a retype. -/
theorem replace_cache_unsound :
    (cacheRun false [.lookup, .retype, .lookup] ⟨0, none, []⟩).found = [false, true] := by decide

end Query.Interrupt
