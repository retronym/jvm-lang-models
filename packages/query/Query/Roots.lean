import Query.Concurrent
/-!
# Two forcers over one lazy store, with claims on roots coarser than facts

`Query.Concurrent` (23 October 2026) gave every fact its own hole and owner. The implementation
that followed, retronym/scala3#84 (`-Yinteractive-parallel`), claims a *root* instead: a symbol
loader's class and its module are one root, a TASTy file is one root, an inherited cache is one
root, a Namer completion's root is its symbol (the design's §3.1, `CompletionRoots`,
`PerKeyClaims`). The claim is reentrant for its owner; another reader that needs any fact of the
root waits on it (`awaitOthers`); a peek at another reader's completion waits too (§4.1,
`isCompletingHereFine`). The implementation then found that a wait-for cycle on roots is often a
lock order and not a dependency cycle (I54, I68, lesson 6 of §11). This file is the model of that.

* **The machine** (§1). The state of `Query.Concurrent` (`CSt`: store, per-fact holes, two
  forcers) plus a claim per root and a poison flag per fact (a root's scratch, §5). `want` is
  `Concurrent.want` with the root between the hole and the rule: a hole of one's own is a cycle, a
  hole or a root of the other's is a wait, a root of one's own is a reentrant entry. A wait that
  would close a wait-for cycle on roots is handled by a `CyclePolicy`: `report` it as a cycle in the
  waiter (the old machine and I54's false errors), `wait` regardless (a deadlock), or `refine`:
  report only a *dependency* cycle (`isDepCycle`: the fact each forcer waits for is on the other's
  stack) and back off otherwise. A peek may `yield`: take the absent path when its wait would close
  a cycle (§4).
* **Linearizability is unaffected by coarseness** (§2). `run_agree`: the same invariant as
  `Concurrent.Inv`, on the `core`, under every schedule, policy and root function.
* **Cycles** (§3). `run_ranked_no_cyc`: under a ranked fixed point, no `.cyc` is reported when the
  policy is `refine` (any roots) or the roots are injective (any policy): a dependency cycle needs a
  fact ranked below itself (`no_dep_cycle`). `waitCycle_unranked` is the old theorem, recovered
  for `root = id` (`closesCycle_id` shows the check is the old one). `lock_order_false_cycle`:
  ranked rules and two coarse roots, and a schedule reports a cycle (I54 as a theorem);
  `lock_order_deadlock`: waiting instead is a deadlock, so the refinement decides *what* to do, not
  *whether*; `lock_order_refine_ok`: backing off gives the sequential answers on every schedule.
* **Peek-tolerated cycles** (§4). `b` peeks `a` while `a` forces `b`, and `a` and `b` peek each
  other (`Interrupt.peekBoth`): sequentially benign in one order or both, under §4.1's rule a
  reported cycle, or a deadlock, with an answer no sequential order gives
  (`peekForce_report_both_fail`, `peekBoth_report_false_cycle`). `peekForce_yield_sequential`,
  `peekBoth_yield_sequential`: a peek that yields when its wait would close a cycle, and a force that
  waits for a peek on the other side to yield, give one of the two sequential answers on every
  schedule. `Concurrent.peek_own_agrees` assumed ranked rules, which exclude these shapes.
* **A root's scratch** (§5). A coarse root carries state beyond its facts' holes
  (`TreeUnpickler.treeAtAddr`'s `PoisonTree` sentinel, set before a definition is read and removed
  after, with no `finally`). `poison_waiter_false_cycle`: an owner aborted inside the root leaves the
  sentinel for the waiter that takes the root over, which reports a false cycle; `scrub_waiter_takes_over`:
  an owner that clears its scratch on unwinding hands the waiter a clean root.
-/

namespace Query.Roots

open Query.Lazy Query.Concurrent
open Interrupt (fact probeEnv PFix PRanked)

variable {Q V R : Type} [DecidableEq Q] [DecidableEq R]

/-! ## 1. The machine -/

/-- What a forcer does when its wait would close a wait-for cycle on roots: report a cycle (the
design's §4.2, I54), wait anyway (a deadlock), or report only a dependency cycle (`isDepCycle`) and
back off otherwise (§11's proposed fix for I68). -/
inductive CyclePolicy | report | wait | refine
  deriving DecidableEq, Repr

/-- The machine's parameters: the root of each fact, the peek mode of `Query.Concurrent`, the
cycle policy, whether a peek yields (§4), whether an unwinding owner scrubs its root's scratch (§5),
and the value a peek answers for a fact in progress. -/
structure Cfg (Q V R : Type) where
  root : Q → R
  mode : PeekMode
  policy : CyclePolicy
  yields : Bool
  scrub : Bool
  absent : V

/-- The state: `Query.Concurrent`'s (store, per-fact holes as `InProgress`, two forcers), a claim
per root with its owner (`CompletionRoots`), and a poison flag per fact: the root's scratch left by
whoever entered the fact, cleared when it is published (§5). -/
structure RSt (Q V R : Type) where
  core : CSt Q V
  claims : R → Option Who
  poison : Q → Bool

/-- Is a probe a peek. -/
def isPeek : Probe Q → Bool
  | .peek _ => true
  | .force _ => false

/-- Is fact `q` on forcer `w`'s stack: `w` is computing it, or a frame above it. -/
def onStack (st : RSt Q V R) (w : Who) (q : Q) : Bool :=
  decide (q ∈ (st.core.get w).frames.map Prod.fst)

/-- The fact forcer `w` is blocked on, if it is: the fact it wants is not finished and its root is
claimed by the other forcer (`Claimant.waitingOn`). -/
def blockedOn (c : Cfg Q V R) (st : RSt Q V R) (w : Who) : Option Q :=
  match (st.core.get w).wants with
  | some p =>
    if (st.core.store (fact p)).isNone ∧ st.claims (c.root (fact p)) = some w.other then some (fact p)
    else none
  | none => none

/-- Would forcer `w`'s waiting on a root the other holds close a wait-for cycle: is the other forcer
blocked on a root `w` holds (`PerKeyClaims.cycleChain`, with two claimants). -/
def closesCycle (c : Cfg Q V R) (st : RSt Q V R) (w : Who) : Bool :=
  (blockedOn c st w.other).isSome

/-- The refinement: a wait-for cycle in which forcer `w`, wanting `q`, and the other forcer each
wait for a fact on the other's stack. Then each is computing what the other needs: a cycle of the
rules, not of the lock order. -/
def isDepCycle (c : Cfg Q V R) (st : RSt Q V R) (w : Who) (q : Q) : Bool :=
  onStack st w.other q &&
    match blockedOn c st w.other with
    | some q' => onStack st w q'
    | none => false

/-- Would forcer `w` wait for fact `q`: it is unfinished and in progress on the other forcer, or
its root is claimed by the other. -/
def wouldWait (c : Cfg Q V R) (st : RSt Q V R) (w : Who) (q : Q) : Bool :=
  (st.core.store q).isNone &&
    (decide (st.core.holes q = some w.other) ||
      ((st.core.holes q).isNone && decide (st.claims (c.root q) = some w.other)))

/-- Is the other forcer's question a peek. -/
def otherWantsPeek (st : RSt Q V R) (w : Who) : Bool :=
  match (st.core.get w.other).wants with
  | some (.peek _) => true
  | _ => false

/-- Release every claim owned by `w`. -/
def releaseClaims (claims : R → Option Who) (w : Who) : R → Option Who :=
  fun r => if claims r = some w then none else claims r

/-- The poison after `w` unwinds: cleared on the facts `w` had in progress if `c.scrub` (a
`finally` around the definition's read), left as it is otherwise (`readIndexedDef` today). -/
def scrubPoison (c : Cfg Q V R) (st : RSt Q V R) (w : Who) : Q → Bool :=
  if c.scrub then fun q => if st.core.holes q = some w then false else st.poison q else st.poison

/-- Unwind forcer `w` (`Concurrent.unwind` with holes released), releasing its claims. -/
def unwindR (c : Cfg Q V R) (w : Who) (o : Option (Out Q V)) (st : RSt Q V R) : RSt Q V R :=
  ⟨unwind true w o st.core, releaseClaims st.claims w, scrubPoison c st w⟩

/-- Forcer `w` backs off: frames dropped, holes and claims released, its demand kept to be retried
(the victim of a lock-order cycle, aborted and its request retried). -/
def backoff (c : Cfg Q V R) (w : Who) (st : RSt Q V R) : RSt Q V R :=
  ⟨{ (st.core.set w ⟨(st.core.get w).demands, [], (st.core.get w).results⟩) with
      holes := releaseAll st.core.holes w },
    releaseClaims st.claims w, scrubPoison c st w⟩

/-- Forcer `w` enters fact `q`'s rule: a frame pushed, the hole taken, the root claimed (a
reentrant claim when `w` holds it already), the scratch poisoned. -/
def enter (Rl : PRules Q V) (c : Cfg Q V R) (w : Who) (q : Q) (st : RSt Q V R) : RSt Q V R :=
  ⟨{ (st.core.set w { st.core.get w with frames := (q, Rl q) :: (st.core.get w).frames }) with
      holes := fun q' => if q' = q then some w else st.core.holes q' },
    fun r => if r = c.root q then some w else st.claims r,
    fun q' => if q' = q then true else st.poison q'⟩

/-- Enter `q`, unless its scratch is poisoned by an owner that is gone: then the false cycle
`readIndexedDef` asserts ("Cyclic reference while unpickling"). -/
def enterOrPoisoned (Rl : PRules Q V) (c : Cfg Q V R) (w : Who) (q : Q) (st : RSt Q V R) : RSt Q V R :=
  if st.poison q then unwindR c w (some (.cyc q)) st else enter Rl c w q st

/-- Forcer `w`, wanting `q`, would close a wait-for cycle. If peeks yield and the other forcer is
at a peek, wait: the other takes the absent path at its next step (§4). Otherwise the policy. -/
def onCycle (c : Cfg Q V R) (w : Who) (q : Q) (st : RSt Q V R) : RSt Q V R :=
  if c.yields && otherWantsPeek st w then st
  else
    match c.policy with
    | .report => unwindR c w (some (.cyc q)) st
    | .wait => st
    | .refine => if isDepCycle c st w q then unwindR c w (some (.cyc q)) st else backoff c w st

/-- Forcer `w` needs fact `q`: read it if finished; a hole of its own is a cycle; a hole of the
other's (`InProgress`, `awaitOthers`) or a root claimed by the other (`acquire`) is a wait, unless
it closes a wait-for cycle; a root of its own is reentrant; else claim and enter. -/
def want (Rl : PRules Q V) (c : Cfg Q V R) (w : Who) (q : Q) (st : RSt Q V R) : RSt Q V R :=
  match st.core.store q with
  | some _ => st
  | none =>
    match st.core.holes q with
    | some w' =>
      if w' = w then unwindR c w (some (.cyc q)) st
      else if closesCycle c st w then onCycle c w q st else st
    | none =>
      match st.claims (c.root q) with
      | some w' =>
        if w' = w then enterOrPoisoned Rl c w q st
        else if closesCycle c st w then onCycle c w q st else st
      | none => enterOrPoisoned Rl c w q st

/-- Forcer `w` publishes `q = v`: stored, hole released, scratch cleared, and the root released
when no frame of `w` is left in it (the claim's `holds` back to 0). -/
def publish (c : Cfg Q V R) (w : Who) (q : Q) (v : V) (rest : List (Frame Q V)) (st : RSt Q V R) :
    RSt Q V R :=
  ⟨{ (st.core.set w { st.core.get w with frames := rest }) with
      store := upd st.core.store q v,
      holes := fun q' => if q' = q then none else st.core.holes q' },
    fun r => if r = c.root q ∧ (rest.any fun fr => decide (c.root fr.1 = r)) = false then none
      else st.claims r,
    fun q' => if q' = q then false else st.poison q'⟩

/-- One force step of forcer `w`: `Concurrent.step` with `want` and `publish` above, and the
yielding peek: a peek that finds the other forcer's hole or root and whose wait would close a
wait-for cycle takes the absent path, as it would sequentially from the owner's side. -/
def step (Rl : PRules Q V) (c : Cfg Q V R) (w : Who) (st : RSt Q V R) : RSt Q V R :=
  match (st.core.get w).frames with
  | [] =>
    match (st.core.get w).demands with
    | [] => st
    | q :: ds =>
      match st.core.store q with
      | some v => { st with core := st.core.set w ⟨ds, [], (st.core.get w).results ++ [(q, .ok v)]⟩ }
      | none => want Rl c w q st
  | (q, .pure v) :: rest => publish c w q v rest st
  | (q, .ask p k) :: rest =>
    match st.core.store (fact p) with
    | some v => { st with core := st.core.set w { st.core.get w with frames := (q, k v) :: rest } }
    | none =>
      if peeksAbsent c.mode w p (st.core.holes (fact p)) ||
          (c.yields && isPeek p && wouldWait c st w (fact p) && closesCycle c st w) then
        { st with core := st.core.set w { st.core.get w with frames := (q, k c.absent) :: rest } }
      else want Rl c w (fact p) st

/-- A scheduler's action (`Concurrent.Act`): a step, or an abort (a cancellation, or the victim
of a cycle), which unwinds with the holes and claims released. -/
def act (Rl : PRules Q V) (c : Cfg Q V R) (st : RSt Q V R) : Act → RSt Q V R
  | .run w => step Rl c w st
  | .abort w => unwindR c w none st

def runActs (Rl : PRules Q V) (c : Cfg Q V R) : List Act → RSt Q V R → RSt Q V R
  | [], st => st
  | x :: xs, st => runActs Rl c xs (act Rl c st x)

/-- Two demand lists, nothing stored, claimed or poisoned. -/
def init (da db : List Q) : RSt Q V R := ⟨Concurrent.init da db, fun _ => none, fun _ => false⟩

/-- A schedule prefix, then a fair tail. -/
def runSched (Rl : PRules Q V) (c : Cfg Q V R) (da db : List Q) (fuel : Nat) (s : List Act) : RSt Q V R :=
  runActs Rl c (s ++ roundRobin fuel) (init da db)

def RSt.idle (st : RSt Q V R) : Bool := st.core.idle
def RSt.answers (st : RSt Q V R) : List (Out Q V) := st.core.answers
def RSt.read (st : RSt Q V R) (qs : List Q) : List (Option V) := st.core.read qs

/-! ## 2. Linearizability: coarseness changes nothing

`Concurrent.Inv` on the core is preserved by every operation: a wait or a back-off leaves the
store and the frames as they were or drops frames, and the root claim never lets a forcer read a
value that is not published. -/

omit [DecidableEq Q] [DecidableEq R] in
theorem unwindR_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {o : Option (Out Q V)}
    {st : RSt Q V R} (h : Inv Rl ρ st.core) (ho : ∀ v, o ≠ some (.ok v)) :
    Inv Rl ρ (unwindR c w o st).core :=
  unwind_inv Rl ρ true w o h ho

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {st : RSt Q V R}
    (h : Inv Rl ρ st.core) : Inv Rl ρ (backoff c w st).core := by
  unfold backoff; dsimp only
  apply Inv.holes
  apply Inv.set Rl ρ h
  · intro fr hfr; simp at hfr
  · exact h.2.2 w

theorem enter_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {q : Q} {st : RSt Q V R}
    (h : Inv Rl ρ st.core) : Inv Rl ρ (enter Rl c w q st).core := by
  unfold enter; dsimp only
  apply Inv.holes
  apply Inv.set Rl ρ h
  · intro fr hfr
    simp only [List.mem_cons] at hfr
    rcases hfr with rfl | hfr
    · exact .refl _
    · exact h.2.1 w fr hfr
  · exact h.2.2 w

theorem enterOrPoisoned_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {q : Q}
    {st : RSt Q V R} (h : Inv Rl ρ st.core) : Inv Rl ρ (enterOrPoisoned Rl c w q st).core := by
  unfold enterOrPoisoned; split
  · exact unwindR_inv h (fun v hv => by cases hv)
  · exact enter_inv h

omit [DecidableEq R] in
theorem onCycle_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {q : Q}
    {st : RSt Q V R} (h : Inv Rl ρ st.core) : Inv Rl ρ (onCycle c w q st).core := by
  unfold onCycle; split
  · exact h
  · split
    · exact unwindR_inv h (fun v hv => by cases hv)
    · exact h
    · split
      · exact unwindR_inv h (fun v hv => by cases hv)
      · exact backoff_inv h

theorem want_inv {Rl : PRules Q V} {ρ : Q → V} {c : Cfg Q V R} {w : Who} {q : Q}
    {st : RSt Q V R} (h : Inv Rl ρ st.core) : Inv Rl ρ (want Rl c w q st).core := by
  unfold want
  split
  · exact h
  · split
    · split
      · exact unwindR_inv h (fun v hv => by cases hv)
      · split
        · exact onCycle_inv h
        · exact h
    · split
      · split
        · exact enterOrPoisoned_inv h
        · split
          · exact onCycle_inv h
          · exact h
      · exact enterOrPoisoned_inv h

/-- **Every step keeps the invariant**, for rules that only force, with a fixed point, whatever
the roots, the policy and the peek flags. -/
theorem step_inv {Rl : PRules Q V} {ρ : Q → V} (hfix : PFix Rl ρ) (hnp : ∀ q, NoPeek (Rl q))
    (c : Cfg Q V R) (w : Who) {st : RSt Q V R} (h : Inv Rl ρ st.core) : Inv Rl ρ (step Rl c w st).core := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold step
  split
  · rename_i hfr
    split
    · exact ⟨h1, h2, h3⟩
    · rename_i q ds hd
      split
      · rename_i v hv
        apply Inv.set Rl ρ ⟨h1, h2, h3⟩
        · intro fr hfr; simp at hfr
        · intro r hr v' hv'
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | hr
          · exact h3 w r hr v' hv'
          · subst hr; simp only [Out.ok.injEq] at hv'; subst hv'; exact h1 q v hv
      · exact want_inv ⟨h1, h2, h3⟩
  · rename_i q v rest hfr
    have hre : Reach (probeEnv ρ) (Rl q) (.pure v) := h2 w (q, .pure v) (by rw [hfr]; simp)
    have hv : v = ρ q := by
      have := hre.run
      simp only [Task.run_pure] at this
      rw [← this, ← hfix q]
    unfold publish; dsimp only
    refine ⟨?_, fun w' => ?_, fun w' => ?_⟩
    · intro x y hx
      simp only [upd] at hx
      split at hx
      · subst_vars; injection hx with hx; exact hx.symm
      · exact h1 x y hx
    · by_cases hw : w' = w
      · subst hw
        show ∀ fr ∈ ((st.core.set w' _).get w').frames, _
        rw [CSt.get_set_same]
        intro fr hfr'
        exact h2 w' fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr')
      · show ∀ fr ∈ ((st.core.set w _).get w').frames, _
        rw [CSt.get_set_other _ _ _ _ hw]; exact h2 w'
    · by_cases hw : w' = w
      · subst hw
        show ∀ r ∈ ((st.core.set w' _).get w').results, _
        rw [CSt.get_set_same]; exact h3 w'
      · show ∀ r ∈ ((st.core.set w _).get w').results, _
        rw [CSt.get_set_other _ _ _ _ hw]; exact h3 w'
  · rename_i q p k rest hfr
    have hre : Reach (probeEnv ρ) (Rl q) (.ask p k) := h2 w (q, .ask p k) (by rw [hfr]; simp)
    have hnp' : NoPeek (Task.ask p k) := NoPeek.reach hre (hnp q)
    obtain ⟨q', hq'⟩ : ∃ q', p = .force q' := by cases hnp' with | ask q' _ _ => exact ⟨q', rfl⟩
    subst hq'
    split
    · rename_i v hv
      apply Inv.set Rl ρ ⟨h1, h2, h3⟩
      · intro fr hfr'
        simp only [List.mem_cons] at hfr'
        rcases hfr' with rfl | hfr'
        · have := hre.step
          simp only [probeEnv, fact] at this
          rw [h1 q' v hv]; exact this
        · exact h2 w fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr')
      · exact h3 w
    · split
      · rename_i hpk; simp [peeksAbsent, isPeek] at hpk
      · exact want_inv ⟨h1, h2, h3⟩

theorem runActs_inv {Rl : PRules Q V} {ρ : Q → V} (hfix : PFix Rl ρ) (hnp : ∀ q, NoPeek (Rl q))
    (c : Cfg Q V R) (xs : List Act) {st : RSt Q V R} (h : Inv Rl ρ st.core) :
    Inv Rl ρ (runActs Rl c xs st).core := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih =>
    cases x with
    | run w => exact ih (step_inv hfix hnp c w h)
    | abort w => exact ih (unwindR_inv h (fun v hv => by cases hv))

/-- **Linearizability, with roots.** For rules that only force and have a fixed point, under every
schedule of steps and aborts, for every root function, policy and peek flags, the store agrees
with the fixed point and every answer either forcer gives is the fixed point's. Coarseness
changes who waits for whom, not what is published: the argument is `Concurrent.run_agree`'s. -/
theorem run_agree {Rl : PRules Q V} {ρ : Q → V} (hfix : PFix Rl ρ) (hnp : ∀ q, NoPeek (Rl q))
    (c : Cfg Q V R) (da db : List Q) (xs : List Act) :
    Agree ρ (runActs Rl c xs (init da db)).core.store ∧
    ∀ w, ∀ r ∈ ((runActs Rl c xs (init da db)).core.get w).results, ∀ v, r.2 = .ok v → v = ρ r.1 :=
  let h := runActs_inv hfix hnp c xs (init_inv Rl ρ da db)
  ⟨h.1, h.2.2⟩

/-! ## 3. Cycles: a dependency cycle is impossible, a lock-order cycle is not

`Concurrent.RInv` on the core (stacks ranked downward, questions below their frames, a hole's
owner has its fact on its stack) is kept by every step, as before. What coarseness adds is two
more invariants: a claim's owner has a fact of that root on its stack (`ClaimInv`), and a poisoned
fact is in progress (`PoisonInv`, when the owner scrubs). The one thing that *fails* to transfer is
`NoCyc`: `Concurrent.want` reported a cycle only when the wanted fact was on the other's stack,
which ranking forbids; here a wait on a root is a wait on *some* fact of it, and ranking says
nothing about that. So `NoCyc` is recovered only where the cycle reported is a dependency cycle:
under `refine`, or when roots are facts. -/

/-- A claim's owner has a fact of the root on its stack: the claim is held while a frame of the
root is live, and released when the last one is published or the forcer unwinds. -/
def ClaimInv (c : Cfg Q V R) (st : RSt Q V R) : Prop :=
  ∀ r w, st.claims r = some w → ∃ q ∈ (st.core.get w).frames.map Prod.fst, c.root q = r

/-- A poisoned fact is in progress: its scratch is cleared when it is published or when its
owner unwinds with `scrub`. -/
def PoisonInv (st : RSt Q V R) : Prop := ∀ q, st.poison q = true → st.core.holes q ≠ none

/-- An injective root function: roots are facts, up to renaming (`root = id`). -/
def Inj (f : Q → R) : Prop := ∀ a b, f a = f b → a = b

/-- The whole invariant under a ranking, with no cycle reported so far. -/
def All (c : Cfg Q V R) (Rl : PRules Q V) (ρ : Q → V) (r : Q → Nat) (st : RSt Q V R) : Prop :=
  RInv Rl ρ r st.core ∧ ClaimInv c st ∧ PoisonInv st ∧ NoCyc st.core

theorem other_other (w : Who) : w.other.other = w := by cases w <;> rfl

omit [DecidableEq Q] [DecidableEq R] in
theorem blockedOn_some {c : Cfg Q V R} {st : RSt Q V R} {w : Who} {q' : Q}
    (h : blockedOn c st w = some q') :
    ∃ p, (st.core.get w).wants = some p ∧ fact p = q' ∧ st.claims (c.root q') = some w.other := by
  unfold blockedOn at h
  split at h
  · rename_i p hp
    split at h
    · rename_i hcond
      injection h with h
      subst h
      exact ⟨p, hp, rfl, hcond.2⟩
    · cases h
  · cases h

omit [DecidableEq Q] [DecidableEq R] in
theorem closesCycle_some {c : Cfg Q V R} {st : RSt Q V R} {w : Who} (h : closesCycle c st w = true) :
    ∃ q', blockedOn c st w.other = some q' := by
  unfold closesCycle at h
  cases hb : blockedOn c st w.other with
  | none => rw [hb] at h; cases h
  | some q' => exact ⟨q', rfl⟩

omit [DecidableEq Q] [DecidableEq R] in
/-- **Two forcers cannot each wait for a fact on the other's stack**: `w`'s question ranks below
its whole stack, which holds the other's question, which ranks below the other's whole stack,
which holds `w`'s question. -/
theorem cycle_impossible {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} {st : RSt Q V R}
    (h : RInv Rl ρ r st.core) {w : Who} {q : Q} {p' : Probe Q}
    (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x)
    (hq : q ∈ (st.core.get w.other).frames.map Prod.fst)
    (hw' : (st.core.get w.other).wants = some p')
    (hq' : fact p' ∈ (st.core.get w).frames.map Prod.fst) : False := by
  have h1 := hlt _ hq'
  have h2 := RInv.wants_lt Rl ρ r h w.other p' hw' q hq
  omega

omit [DecidableEq R] in
/-- **A dependency cycle never forms under a ranked invariant**: whatever the roots, the
refinement's test is false at every reachable state, so a forcer that reports a cycle only when
`isDepCycle` holds never reports one under a ranked fixed point. -/
theorem no_dep_cycle {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (c : Cfg Q V R) {st : RSt Q V R}
    (h : RInv Rl ρ r st.core) (w : Who) (p : Probe Q) (hw : (st.core.get w).wants = some p) :
    isDepCycle c st w (fact p) = false := by
  cases hd : isDepCycle c st w (fact p) with
  | false => rfl
  | true =>
    exfalso
    cases hb : blockedOn c st w.other with
    | none => simp [isDepCycle, hb] at hd
    | some q' =>
      simp only [isDepCycle, hb, Bool.and_eq_true, onStack, decide_eq_true_eq] at hd
      obtain ⟨p', hw', hfp, _⟩ := blockedOn_some hb
      exact cycle_impossible h (RInv.wants_lt Rl ρ r h w p hw) hd.1 hw' (by rw [hfp]; exact hd.2)

/-! ### Preservation of the three invariants -/

omit [DecidableEq Q] [DecidableEq R] in
theorem unwindR_claim {c : Cfg Q V R} {w : Who} {o : Option (Out Q V)} {st : RSt Q V R}
    (hcl : ClaimInv c st) : ClaimInv c (unwindR c w o st) := by
  intro r w' h
  simp only [unwindR, releaseClaims] at h
  split at h
  · cases h
  · rename_i hne
    have hw : w' ≠ w := fun e => hne (e ▸ h)
    show ∃ q ∈ ((unwind true w o st.core).get w').frames.map Prod.fst, _
    rw [unwind_get_other _ _ _ _ _ hw]
    exact hcl r w' h

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_claim {c : Cfg Q V R} {w : Who} {st : RSt Q V R}
    (hcl : ClaimInv c st) : ClaimInv c (backoff c w st) := by
  intro r w' h
  simp only [backoff, releaseClaims] at h
  split at h
  · cases h
  · rename_i hne
    have hw : w' ≠ w := fun e => hne (e ▸ h)
    simp only [backoff, CSt.get_holes, CSt.get_set_other _ _ _ _ hw]
    exact hcl r w' h

theorem enter_claim {Rl : PRules Q V} {c : Cfg Q V R} {w : Who} {q : Q} {st : RSt Q V R}
    (hcl : ClaimInv c st) : ClaimInv c (enter Rl c w q st) := by
  intro r w' h
  simp only [enter] at h ⊢
  split at h
  · rename_i hr; injection h with h; subst h; subst hr
    exact ⟨q, by simp [CSt.get_holes, CSt.get_set_same], rfl⟩
  · obtain ⟨q', hq', hr⟩ := hcl r w' h
    by_cases hw : w' = w
    · subst hw
      simp only [CSt.get_holes, CSt.get_set_same, List.map_cons, List.mem_cons]
      exact ⟨q', Or.inr hq', hr⟩
    · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]; exact ⟨q', hq', hr⟩

theorem publish_claim {c : Cfg Q V R} {w : Who} {q : Q} {v : V} {t : Task (Probe Q) (fun _ => V) V}
    {rest : List (Frame Q V)} {st : RSt Q V R} (hcl : ClaimInv c st)
    (hfr : (st.core.get w).frames = (q, t) :: rest) : ClaimInv c (publish c w q v rest st) := by
  intro r w' h
  simp only [publish] at h ⊢
  split at h
  · cases h
  · rename_i hcond
    obtain ⟨q', hq', hr⟩ := hcl r w' h
    by_cases hw : w' = w
    · subst hw
      simp only [CSt.get_store_holes, CSt.get_set_same]
      rw [hfr] at hq'
      simp only [List.map_cons, List.mem_cons] at hq'
      rcases hq' with rfl | hq'
      · by_cases hany : (rest.any fun fr => decide (c.root fr.1 = r)) = true
        · simp only [List.any_eq_true, decide_eq_true_eq] at hany
          obtain ⟨fr, hfr', hfr''⟩ := hany
          exact ⟨fr.1, List.mem_map.mpr ⟨fr, hfr', rfl⟩, hfr''⟩
        · exact absurd ⟨hr.symm, by simpa using hany⟩ hcond
      · exact ⟨q', hq', hr⟩
    · simp only [CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact ⟨q', hq', hr⟩

omit [DecidableEq Q] [DecidableEq R] in
theorem set_claim {c : Cfg Q V R} {w : Who} {st : RSt Q V R} (hcl : ClaimInv c st) (f : Forcer Q V)
    (hf : ∀ q ∈ (st.core.get w).frames.map Prod.fst, q ∈ f.frames.map Prod.fst) :
    ClaimInv c { st with core := st.core.set w f } := by
  intro r w' h
  obtain ⟨q, hq, hr⟩ := hcl r w' h
  by_cases hw : w' = w
  · subst hw; exact ⟨q, by simp only [CSt.get_set_same]; exact hf q hq, hr⟩
  · exact ⟨q, by simp only [CSt.get_set_other _ _ _ _ hw]; exact hq, hr⟩

omit [DecidableEq Q] [DecidableEq R] in
theorem release_poison {c : Cfg Q V R} {w : Who} {st : RSt Q V R} (hs : c.scrub = true)
    (hp : PoisonInv st) : ∀ q, scrubPoison c st w q = true → releaseAll st.core.holes w q ≠ none := by
  intro q h
  simp only [scrubPoison, hs, ↓reduceIte] at h
  simp only [releaseAll]
  split at h
  · cases h
  · rename_i hne; simp only [hne, ↓reduceIte]; exact hp q h

omit [DecidableEq Q] [DecidableEq R] in
theorem unwindR_poison {c : Cfg Q V R} {w : Who} {o : Option (Out Q V)} {st : RSt Q V R}
    (hs : c.scrub = true) (hp : PoisonInv st) : PoisonInv (unwindR c w o st) := by
  intro q h
  show (unwind true w o st.core).holes q ≠ none
  rw [unwind_holes]; simp only [↓reduceIte]
  exact release_poison hs hp q h

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_poison {c : Cfg Q V R} {w : Who} {st : RSt Q V R}
    (hs : c.scrub = true) (hp : PoisonInv st) : PoisonInv (backoff c w st) :=
  fun q h => release_poison hs hp q h

theorem enter_poison {Rl : PRules Q V} {c : Cfg Q V R} {w : Who} {q : Q} {st : RSt Q V R}
    (hp : PoisonInv st) : PoisonInv (enter Rl c w q st) := by
  intro q' h
  simp only [enter] at h ⊢
  split at h
  · rename_i hq; simp only [hq, ↓reduceIte]; exact nofun
  · rename_i hq; simp only [hq, ↓reduceIte]; exact hp q' h

theorem publish_poison {c : Cfg Q V R} {w : Who} {q : Q} {v : V} {rest : List (Frame Q V)}
    {st : RSt Q V R} (hp : PoisonInv st) : PoisonInv (publish c w q v rest st) := by
  intro q' h
  simp only [publish] at h ⊢
  split at h
  · cases h
  · rename_i hq; simp only [hq, ↓reduceIte]; exact hp q' h

omit [DecidableEq Q] [DecidableEq R] in
theorem set_poison {w : Who} {st : RSt Q V R} (hp : PoisonInv st) (f : Forcer Q V) :
    PoisonInv { st with core := st.core.set w f } := by
  intro q h; show (st.core.set w f).holes q ≠ none; rw [CSt.holes_set]; exact hp q h

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_nocyc {c : Cfg Q V R} {w : Who} {st : RSt Q V R} (hc : NoCyc st.core) :
    NoCyc (backoff c w st).core := by
  intro w' rr hrr
  simp only [backoff] at hrr
  by_cases hw : w' = w
  · subst hw; simp only [CSt.get_holes, CSt.get_set_same] at hrr; exact hc w' rr hrr
  · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw] at hrr; exact hc w' rr hrr

theorem enter_nocyc {Rl : PRules Q V} {c : Cfg Q V R} {w : Who} {q : Q} {st : RSt Q V R}
    (hc : NoCyc st.core) : NoCyc (enter Rl c w q st).core := by
  intro w' rr hrr
  simp only [enter] at hrr
  by_cases hw : w' = w
  · subst hw; simp only [CSt.get_holes, CSt.get_set_same] at hrr; exact hc w' rr hrr
  · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw] at hrr; exact hc w' rr hrr

omit [DecidableEq Q] [DecidableEq R] in
theorem abort_nocyc {c : Cfg Q V R} {w : Who} {st : RSt Q V R} (hc : NoCyc st.core) :
    NoCyc (unwindR c w none st).core := by
  intro w' rr hrr
  simp only [unwindR] at hrr
  by_cases hw : w' = w
  · subst hw
    rw [unwind_get_same] at hrr
    rcases unwindForcer_results _ _ rr hrr with hrr | ⟨_, h', _⟩
    · exact hc w' rr hrr
    · cases h'
  · rw [unwind_get_other _ _ _ _ _ hw] at hrr; exact hc w' rr hrr

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_rinv {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} {c : Cfg Q V R} {w : Who}
    {st : RSt Q V R} (h : RInv Rl ρ r st.core) : RInv Rl ρ r (backoff c w st).core := by
  have hinv : Inv Rl ρ (backoff c w st).core := backoff_inv h.1
  obtain ⟨_, h2, h3, h4⟩ := h
  unfold backoff at hinv ⊢; dsimp only at hinv ⊢
  refine ⟨hinv, fun w' => ?_, fun w' => ?_, fun q w' hq => ?_⟩
  · by_cases hw : w' = w
    · subst hw; simp only [CSt.get_holes, CSt.get_set_same]; trivial
    · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]; exact h2 w'
  · by_cases hw : w' = w
    · subst hw; simp only [CSt.get_holes, CSt.get_set_same]; simp
    · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]; exact h3 w'
  · simp only [releaseAll] at hq
    split at hq
    · cases hq
    · rename_i hne
      have hw : w' ≠ w := fun e => hne (e ▸ hq)
      simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]
      exact h4 q w' hq

theorem enter_rinv {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hr : PRanked Rl ρ r) {c : Cfg Q V R}
    {w : Who} {q : Q} {st : RSt Q V R} (h : RInv Rl ρ r st.core)
    (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x) :
    RInv Rl ρ r (enter Rl c w q st).core := by
  have hinv : Inv Rl ρ (enter Rl c w q st).core := enter_inv h.1
  obtain ⟨_, h2, h3, h4⟩ := h
  unfold enter at hinv ⊢; dsimp only at hinv ⊢
  refine ⟨hinv, ?_, ?_, ?_⟩
  · intro w'
    by_cases hw : w' = w
    · subst hw
      simp only [CSt.get_holes, CSt.get_set_same]
      rcases hf : (st.core.get w').frames with _ | ⟨f₂, rest⟩
      · trivial
      · refine ⟨hlt f₂.1 (by rw [hf]; simp), ?_⟩
        have := h2 w'; rw [hf] at this; exact this
    · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]; exact h2 w'
  · intro w' fr hfr p k hpk
    by_cases hw : w' = w
    · subst hw
      simp only [CSt.get_holes, CSt.get_set_same, List.mem_cons] at hfr
      rcases hfr with rfl | hfr
      · simp only at hpk
        exact hr q p (by rw [hpk]; simp [Task.trace])
      · exact h3 w' fr hfr p k hpk
    · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw] at hfr; exact h3 w' fr hfr p k hpk
  · intro x w' hx
    simp only at hx
    split at hx
    · subst_vars; injection hx with hx; subst hx
      simp [CSt.get_holes, CSt.get_set_same]
    · have := h4 x w' hx
      by_cases hw : w' = w
      · subst hw; simp only [CSt.get_holes, CSt.get_set_same, List.map_cons, List.mem_cons]; exact Or.inr this
      · simp only [CSt.get_holes, CSt.get_set_other _ _ _ _ hw]; exact this

/-! ### The operations keep `All`, where they are reachable -/

omit [DecidableEq Q] [DecidableEq R] in
theorem abort_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} {w : Who}
    {st : RSt Q V R} (hs : c.scrub = true) (h : All c Rl ρ r st) : All c Rl ρ r (unwindR c w none st) :=
  ⟨unwind_rinv Rl ρ r w none h.1 (fun v hv => by cases hv), unwindR_claim h.2.1,
    unwindR_poison hs h.2.2.1, abort_nocyc h.2.2.2⟩

omit [DecidableEq Q] [DecidableEq R] in
theorem backoff_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} {w : Who}
    {st : RSt Q V R} (hs : c.scrub = true) (h : All c Rl ρ r st) : All c Rl ρ r (backoff c w st) :=
  ⟨backoff_rinv h.1, backoff_claim h.2.1, backoff_poison hs h.2.2.1, backoff_nocyc h.2.2.2⟩

theorem enter_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hr : PRanked Rl ρ r)
    {w : Who} {q : Q} {st : RSt Q V R} (h : All c Rl ρ r st)
    (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x) : All c Rl ρ r (enter Rl c w q st) :=
  ⟨enter_rinv hr h.1 hlt, enter_claim h.2.1, enter_poison h.2.2.1, enter_nocyc h.2.2.2⟩

theorem enterOrPoisoned_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat}
    (hr : PRanked Rl ρ r) {w : Who} {q : Q} {st : RSt Q V R} (h : All c Rl ρ r st)
    (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x) (hh : st.core.holes q = none) :
    All c Rl ρ r (enterOrPoisoned Rl c w q st) := by
  unfold enterOrPoisoned; split
  · rename_i hpz; exfalso; exact h.2.2.1 q hpz hh
  · exact enter_all hr h hlt

omit [DecidableEq R] in
/-- **Closing a wait-for cycle never reports one** under a ranked invariant, when the policy
refines (the report needs a dependency cycle, which `cycle_impossible` forbids) or the roots are
injective (then every claim held is a fact on the stack, so the cycle *is* a dependency cycle). -/
theorem onCycle_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} {w : Who} {q : Q}
    {st : RSt Q V R} (hs : c.scrub = true) (hpol : c.policy ≠ .report ∨ Inj c.root)
    (h : All c Rl ρ r st) (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x)
    (hclose : closesCycle c st w = true)
    (hq : Inj c.root → q ∈ (st.core.get w.other).frames.map Prod.fst) :
    All c Rl ρ r (onCycle c w q st) := by
  obtain ⟨q', hq'⟩ := closesCycle_some hclose
  obtain ⟨p', hw', hfp, hcl'⟩ := blockedOn_some hq'
  unfold onCycle
  split
  · exact h
  · split
    · rename_i hpr
      exfalso
      have hinj : Inj c.root := by rcases hpol with hh | hh; exact absurd hpr hh; exact hh
      obtain ⟨q'', hq'', hroot⟩ := h.2.1 _ _ hcl'
      rw [other_other] at hq''
      have hq'w : q' ∈ (st.core.get w).frames.map Prod.fst := by rw [← hinj _ _ hroot]; exact hq''
      exact cycle_impossible h.1 hlt (hq hinj) hw' (by rw [hfp]; exact hq'w)
    · exact h
    · split
      · rename_i hdep; exfalso
        simp only [isDepCycle, Bool.and_eq_true, onStack, decide_eq_true_eq, hq'] at hdep
        exact cycle_impossible h.1 hlt hdep.1 hw' (by rw [hfp]; exact hdep.2)
      · exact backoff_all hs h

theorem want_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hr : PRanked Rl ρ r)
    (hs : c.scrub = true) (hpol : c.policy ≠ .report ∨ Inj c.root) {w : Who} {q : Q} {st : RSt Q V R}
    (h : All c Rl ρ r st) (hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x) :
    All c Rl ρ r (want Rl c w q st) := by
  unfold want
  split
  · exact h
  · split
    · rename_i w' hw'
      split
      · rename_i heq; subst heq; exfalso
        have := hlt q (h.1.2.2.2 q w' hw')
        omega
      · rename_i hne
        have hwo : w' = w.other := Who.other_of_ne hne
        subst hwo
        split
        · rename_i hclose
          exact onCycle_all hs hpol h hlt hclose (fun _ => h.1.2.2.2 q w.other hw')
        · exact h
    · rename_i hh
      split
      · rename_i w' hcl'
        split
        · rename_i heq; subst heq
          exact enterOrPoisoned_all hr h hlt hh
        · rename_i hne
          have hwo : w' = w.other := Who.other_of_ne hne
          subst hwo
          split
          · rename_i hclose
            refine onCycle_all hs hpol h hlt hclose (fun hinj => ?_)
            obtain ⟨q'', hq'', hroot⟩ := h.2.1 _ _ hcl'
            rw [← hinj _ _ hroot]; exact hq''
          · exact h
      · exact enterOrPoisoned_all hr h hlt hh

/-- **Every step keeps `All`**: the ranked invariant, the claim and poison invariants, and no cycle
reported, under a ranked fixed point of force-only rules, with scrubbing, when the policy refines
or the roots are injective. -/
theorem step_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hfix : PFix Rl ρ)
    (hr : PRanked Rl ρ r) (hnp : ∀ q, NoPeek (Rl q)) (hs : c.scrub = true)
    (hpol : c.policy ≠ .report ∨ Inj c.root) (w : Who) {st : RSt Q V R} (h : All c Rl ρ r st) :
    All c Rl ρ r (step Rl c w st) := by
  obtain ⟨hri, hcl, hp, hc⟩ := h
  have hinv := step_inv hfix hnp c w hri.1
  obtain ⟨h1, h2, h3, h4⟩ := hri
  unfold step at hinv ⊢
  split
  · rename_i hfr
    rw [hfr] at hinv
    split
    · exact ⟨⟨h1, h2, h3, h4⟩, hcl, hp, hc⟩
    · rename_i q ds hd
      split
      · rename_i v hv
        simp only [hd, hv] at hinv
        refine ⟨⟨hinv, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩,
          set_claim hcl _ (by rw [hfr]; simp), set_poison hp _, fun w' rr hrr => ?_⟩
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
      · rename_i hs'
        have hw : (st.core.get w).wants = some (.force q) := by
          rcases hf : st.core.get w with ⟨ds', fr', rs'⟩
          rw [hf] at hfr hd; simp only at hfr hd; subst hfr hd; rfl
        have hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q < r x := by
          have := RInv.wants_lt Rl ρ r ⟨h1, h2, h3, h4⟩ w _ hw; simpa [fact] using this
        exact want_all hr hs hpol ⟨⟨h1, h2, h3, h4⟩, hcl, hp, hc⟩ hlt
  · rename_i q v rest hfr
    rw [hfr] at hinv
    refine ⟨⟨hinv, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩, publish_claim hcl hfr,
      publish_poison hp, fun w' rr hrr => ?_⟩
    · by_cases hw : w' = w
      · subst hw; simp only [publish, CSt.get_store_holes, CSt.get_set_same]
        have := h2 w'; rw [hfr] at this; exact this.tail
      · simp only [publish, CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact h2 w'
    · by_cases hw : w' = w
      · subst hw; simp only [publish, CSt.get_store_holes, CSt.get_set_same]
        intro fr hfr' p k hpk; exact h3 w' fr (by rw [hfr]; exact List.mem_cons_of_mem _ hfr') p k hpk
      · simp only [publish, CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact h3 w'
    · simp only [publish] at hx
      split at hx
      · cases hx
      · rename_i hne
        have := h4 x w' hx
        by_cases hw : w' = w
        · subst hw
          simp only [publish, CSt.get_store_holes, CSt.get_set_same]
          rw [hfr] at this
          simp only [List.map_cons, List.mem_cons] at this
          rcases this with h | h
          · exact absurd h hne
          · exact h
        · simp only [publish, CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw]; exact this
    · by_cases hw : w' = w
      · subst hw; simp only [publish, CSt.get_store_holes, CSt.get_set_same] at hrr; exact hc w' rr hrr
      · simp only [publish, CSt.get_store_holes, CSt.get_set_other _ _ _ _ hw] at hrr; exact hc w' rr hrr
  · rename_i q p k rest hfr
    have hre : Reach (probeEnv ρ) (Rl q) (.ask p k) := h1.2.1 w (q, .ask p k) (by rw [hfr]; simp)
    have hnp' : NoPeek (Task.ask p k) := NoPeek.reach hre (hnp q)
    obtain ⟨q', hq'⟩ : ∃ q', p = .force q' := by cases hnp' with | ask q' _ _ => exact ⟨q', rfl⟩
    subst hq'
    have hw : (st.core.get w).wants = some (.force q') := by
      rcases hf : st.core.get w with ⟨ds', fr', rs'⟩
      rw [hf] at hfr; simp only at hfr; subst hfr; rfl
    have hlt : ∀ x ∈ (st.core.get w).frames.map Prod.fst, r q' < r x := by
      have := RInv.wants_lt Rl ρ r ⟨h1, h2, h3, h4⟩ w _ hw; simpa [fact] using this
    rw [hfr] at hinv
    split
    · rename_i v hv
      have hv' : st.core.store q' = some v := hv
      simp only [fact, hv'] at hinv
      refine ⟨⟨hinv, fun w' => ?_, fun w' => ?_, fun x w' hx => ?_⟩,
        set_claim hcl _ (by rw [hfr]; simp), set_poison hp _, fun w' rr hrr => ?_⟩
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
            simp only [probeEnv, fact] at hre'
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
    · split
      · rename_i hpk; simp [peeksAbsent, isPeek] at hpk
      · exact want_all hr hs hpol ⟨⟨h1, h2, h3, h4⟩, hcl, hp, hc⟩ hlt

theorem runActs_all {c : Cfg Q V R} {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hfix : PFix Rl ρ)
    (hr : PRanked Rl ρ r) (hnp : ∀ q, NoPeek (Rl q)) (hs : c.scrub = true)
    (hpol : c.policy ≠ .report ∨ Inj c.root) (xs : List Act) {st : RSt Q V R} (h : All c Rl ρ r st) :
    All c Rl ρ r (runActs Rl c xs st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih =>
    cases x with
    | run w => exact ih (step_all hfix hr hnp hs hpol w h)
    | abort w => exact ih (abort_all hs h)

omit [DecidableEq Q] [DecidableEq R] in
theorem init_all (c : Cfg Q V R) (Rl : PRules Q V) (ρ : Q → V) (r : Q → Nat) (da db : List Q) :
    All c Rl ρ r (init da db) :=
  ⟨init_rinv Rl ρ r da db, (fun _ _ h => by cases h), (fun _ h => by cases h),
    (by intro w; cases w <;> simp [init, Concurrent.init, CSt.get])⟩

/-- **Under a ranked fixed point no schedule reports a cycle, when a reported cycle is a
dependency cycle**: the policy refines (any roots), or the roots are injective (any policy, the
old machine's `run_ranked_no_cyc`). The owner must scrub its scratch on unwinding (§5). -/
theorem run_ranked_no_cyc {Rl : PRules Q V} {ρ : Q → V} {r : Q → Nat} (hfix : PFix Rl ρ)
    (hr : PRanked Rl ρ r) (hnp : ∀ q, NoPeek (Rl q)) (c : Cfg Q V R) (hs : c.scrub = true)
    (hpol : c.policy ≠ .report ∨ Inj c.root) (da db : List Q) (xs : List Act) :
    NoCyc (runActs Rl c xs (init da db)).core :=
  (runActs_all hfix hr hnp hs hpol xs (init_all c Rl ρ r da db)).2.2.2

/-- **A reported dependency cycle is a cycle of the rules**: with the refining policy, a `.cyc`
under some schedule means the rules have no ranked fixed point, whatever the roots. Raising
`CyclicReference` on a dependency cycle is sound. -/
theorem depCycle_unranked {Rl : PRules Q V} (hnp : ∀ q, NoPeek (Rl q)) (c : Cfg Q V R)
    (hs : c.scrub = true) (hpol : c.policy = .refine) (da db : List Q) (xs : List Act) (w : Who)
    (q : Q) (rr : Q × Out Q V) (hm : rr ∈ ((runActs Rl c xs (init da db)).core.get w).results)
    (hc : rr.2 = .cyc q) : ∀ ρ r, PFix Rl ρ → ¬ PRanked Rl ρ r :=
  fun ρ r hfix hr =>
    run_ranked_no_cyc (ρ := ρ) (r := r) hfix hr hnp c hs (Or.inl (by rw [hpol]; exact nofun)) da db xs w rr hm q hc

/-- **With roots that are facts, `Concurrent.waitCycle_unranked` holds again**, under every
policy: a wait-for cycle on injective roots is a dependency cycle. -/
theorem waitCycle_unranked {Rl : PRules Q V} (hnp : ∀ q, NoPeek (Rl q)) (c : Cfg Q V R)
    (hs : c.scrub = true) (hinj : Inj c.root) (da db : List Q) (xs : List Act) (w : Who) (q : Q)
    (rr : Q × Out Q V) (hm : rr ∈ ((runActs Rl c xs (init da db)).core.get w).results)
    (hc : rr.2 = .cyc q) : ∀ ρ r, PFix Rl ρ → ¬ PRanked Rl ρ r :=
  fun ρ r hfix hr => run_ranked_no_cyc (ρ := ρ) (r := r) hfix hr hnp c hs (Or.inr hinj) da db xs w rr hm q hc

omit [DecidableEq Q] in
/-- **With `root = id` the wait-for check is the old one.** When the claims are the holes (as they
are with one fact per root) and a hole means an unfinished fact, `closesCycle` and
`Concurrent.closesCycle` agree. -/
theorem closesCycle_id (c : Cfg Q V Q) (hid : ∀ q, c.root q = q) (st : RSt Q V Q)
    (hcl : st.claims = st.core.holes) (hns : ∀ q w', st.core.holes q = some w' → st.core.store q = none)
    (w : Who) : closesCycle c st w = Concurrent.closesCycle st.core w := by
  cases h : Concurrent.closesCycle st.core w with
  | true =>
    unfold Concurrent.closesCycle at h
    split at h
    · rename_i p hp
      simp only [decide_eq_true_eq] at h
      unfold closesCycle blockedOn; rw [hp]
      have hs : (st.core.store (fact p)).isNone = true := by rw [hns _ _ h]; rfl
      simp [hs, hid, hcl, other_other, h]
    · cases h
  | false =>
    cases h' : closesCycle c st w with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨q', hq'⟩ := closesCycle_some h'
      obtain ⟨p, hw, hfp, hc⟩ := blockedOn_some hq'
      unfold Concurrent.closesCycle at h; rw [hw] at h
      rw [hid, hcl, other_other] at hc; subst hfp
      simp [hc] at h

/-! ## 4. The scenarios, by `decide` over every schedule

### A lock order on two coarse roots (I54, lesson 6)

Two roots of two facts each, `ra = {a1, a2}` and `rb = {b1, b2}`; `a1` needs `b2` and `b1` needs
`a2`. At fact level the dependencies are a forest: ranked, and `forceAll` in either order succeeds.
Two forcers, one on `a1` and one on `b1`, each hold a root the other needs a fact of: a wait-for
cycle on roots that no sequential order has. This is two readers completing `Settings.Setting`'s
members in opposite orders (I68), and the TASTy file root of I54. -/

inductive L4 | a1 | a2 | b1 | b2
  deriving DecidableEq, Repr

inductive R2 | ra | rb
  deriving DecidableEq, Repr

/-- Two facts per root. -/
def rootL : L4 → R2
  | .a1 => .ra
  | .a2 => .ra
  | .b1 => .rb
  | .b2 => .rb

/-- `a1` forces `b2`, `b1` forces `a2`: cross dependencies, no cycle. -/
def lockP : PRules L4 String
  | .a1 => forces .b2 fun v => .pure s!"a1({v})"
  | .b1 => forces .a2 fun v => .pure s!"b1({v})"
  | .a2 => .pure "a2"
  | .b2 => .pure "b2"

/-- The fixed point of `lockP`. -/
def ρL : L4 → String
  | .a1 => "a1(b2)"
  | .b1 => "b1(a2)"
  | .a2 => "a2"
  | .b2 => "b2"

/-- A ranking of `lockP`. -/
def rL : L4 → Nat
  | .a1 => 1
  | .b1 => 1
  | .a2 => 0
  | .b2 => 0

/-- Coarse roots, peeks wait, no scratch left behind. -/
def cfgL (pol : CyclePolicy) : Cfg L4 String R2 := ⟨rootL, .own, pol, false, true, "absent"⟩

/-- **The lock-order rules are ranked**: a fixed point with a strictly decreasing rank. -/
theorem lock_ranked : PFix lockP ρL ∧ PRanked lockP ρL rL :=
  ⟨fun q => by cases q <;> decide, fun q => by cases q <;> decide⟩

/-- **Sequentially both orders succeed**: no cycle, the same store. -/
theorem lock_sequential_ok :
    (sequential lockP "absent" 9 [.a1] [.b1]).1 = [.ok "a1(b2)", .ok "b1(a2)"] ∧
    (sequential lockP "absent" 9 [.b1] [.a1]).1 = [.ok "b1(a2)", .ok "a1(b2)"] := by
  decide

/-- **I54 as a theorem: ranked rules, coarse roots, a reported cycle.** Each forcer enters its
root; the first then needs `b2`, whose root the second holds, and the second is blocked on `a2`,
whose root the first holds: the first's wait would close a wait-for cycle, and the `report` policy
makes it a `.cyc` at `b2`, an error no sequential order gives ("Cyclic reference involving class
Setting"). The second forcer finishes. -/
theorem lock_order_false_cycle :
    let st := runSched lockP (cfgL .report) [.a1] [.b1] 30 [.run .a, .run .b, .run .a]
    st.idle = true ∧ st.core.fa.results = [(.a1, .cyc .b2)] ∧ st.core.fb.results = [(.b1, .ok "b1(a2)")] := by
  decide +kernel

/-- **The same schedule under `refine`** finds no dependency edge (`b2` is not on the second
forcer's stack, only its root is held) and backs the first forcer off instead; it retries and both
answer as the sequential run does. -/
theorem lock_order_refine_backs_off :
    let st := runSched lockP (cfgL .refine) [.a1] [.b1] 30 [.run .a, .run .b, .run .a]
    st.idle = true ∧ st.core.fa.results = [(.a1, .ok "a1(b2)")] ∧ st.core.fb.results = [(.b1, .ok "b1(a2)")] := by
  decide +kernel

/-- **A lock-order cycle is still a deadlock.** Waiting through it (`wait`) leaves both forcers
blocked for the rest of the run: the refinement decides *what* to do with the cycle (report or back
off), not *whether* something must be done. -/
theorem lock_order_deadlock :
    let st := runSched lockP (cfgL .wait) [.a1] [.b1] 30 [.run .a, .run .b]
    st.idle = false ∧ st.core.fa.results = [] ∧ st.core.fb.results = [] ∧
      st.core.fa.frames.length = 1 ∧ st.core.fb.frames.length = 1 := by
  decide +kernel

/-- **Backing off gives the sequential answers on every schedule**: under `refine`, all 64
schedules of six steps and a fair tail finish with the sequential answers and store. -/
theorem lock_order_refine_ok :
    ∀ s ∈ scheds 6,
      let st := runSched lockP (cfgL .refine) [.a1] [.b1] 30 s
      st.idle = true ∧ st.answers = (sequential lockP "absent" 9 [.a1] [.b1]).1 ∧
        st.read [.a1, .a2, .b1, .b2] = [.a1, .a2, .b1, .b2].map (sequential lockP "absent" 9 [.a1] [.b1]).2 := by
  decide +kernel

/-! ### The true cross-thread cycle under `refine`

`Concurrent.crossP`: `a` needs `b` and `b` needs `a`, roots are facts. The refinement keeps the
report: when the first forcer's wait on `b` would close the cycle, `b` is on the second's stack and
`a` on the first's, a dependency cycle, so both report as in `cross_cycle_both_report`. -/

/-- Roots are facts (`id`), the refining policy. -/
def cfgX : Cfg X3 String X3 := ⟨id, .own, .refine, false, true, "absent"⟩

/-- **`refine` still reports the dependency cycle**, on every schedule: both report, nothing on
the cycle is stored, `c` is. -/
theorem cross_refine_both_report :
    ∀ s ∈ scheds 6,
      let st := runSched crossP cfgX [.a, .c] [.b, .c] 30 s
      st.idle = true ∧
        (st.core.fa.results.map (fun r => match r.2 with | .cyc _ => true | _ => false)) = [true, false] ∧
        (st.core.fb.results.map (fun r => match r.2 with | .cyc _ => true | _ => false)) = [true, false] ∧
        st.read [.a, .b, .c] = [none, none, some "c"] := by
  decide +kernel

/-! ### Peek-tolerated cycles (the hypothesis for I68)

Sequentially a cycle through a peek is benign when the peek meets its own hole: `forcePeek`
answers `absent` and the frames above publish. With §4.1's rule (a peek at the other reader's
completion waits), two forcers entering the pair from opposite sides each meet the other's hole:
a wait-for cycle on facts, and the `report` policy raises it, or the `wait` policy deadlocks.
`Concurrent.peek_own_agrees` assumed ranked rules, which excludes both shapes below: read as forces
they are cycles. -/

inductive PF | a | b
  deriving DecidableEq, Repr

/-- `a` forces `b`; `b` peeks `a`. -/
def peekForceP : PRules PF String
  | .a => forces .b fun v => .pure s!"a({v})"
  | .b => .ask (.peek .a) fun v => .pure s!"b({v})"

/-- Roots are facts; peeks see their own holes and wait on the other's; `yields` is the remedy. -/
def cfgP (pol : CyclePolicy) (yields : Bool) : Cfg PF String PF := ⟨id, .own, pol, yields, true, "absent"⟩

/-- **Sequentially the force-peek pair is benign in one order only.** From `a`: `b`'s peek meets
`a`'s hole, `b = b(absent)`, `a = a(b(absent))`. From `b`: the peek finds `a` not in progress and
forces it, `a` forces `b`, a cycle at `b`; `a` is then answered from the other side. So one of the
two sequential answers has a cycle: the hypothesis "no sequential order reports a cycle" fails
for this shape (see `peekBoth_*` for the shape where it holds). -/
theorem peekForce_sequential :
    (forcePeekAll peekForceP "absent" 9 [.a, .b] (fun _ => none)).1 = [.ok "a(b(absent))", .ok "b(absent)"] ∧
    (forcePeekAll peekForceP "absent" 9 [.b, .a] (fun _ => none)).1 = [.cyc .b, .ok "a(b(absent))"] := by
  decide

/-- **Under §4.1 and §4.2 as written, both demands can fail.** Each forcer enters its fact; the
first, forcing `b`, finds the second blocked on `a` (its peek waits) and reports the cycle at `b`,
releasing `a`; the second's peek then enters `a`, which forces `b`, its own hole: a second cycle.
Neither sequential order fails both. The forcer that reports is the one whose wait closes the
cycle, a property of the schedule, not of the rules. -/
theorem peekForce_report_both_fail :
    let st := runSched peekForceP (cfgP .report false) [.a] [.b] 30 [.run .a, .run .b, .run .a, .run .b]
    st.idle = true ∧ st.core.fa.results = [(.a, .cyc .b)] ∧ st.core.fb.results = [(.b, .cyc .b)] ∧
      st.read [.a, .b] = [none, none] := by
  decide +kernel

/-- The other order of checks: the second forcer's peek closes the cycle and reports, the first
then completes both; the sequential answer from `b`'s side, up to the fact named. -/
theorem peekForce_report_other_site :
    let st := runSched peekForceP (cfgP .report false) [.a] [.b] 30 [.run .a, .run .b, .run .b, .run .a]
    st.idle = true ∧ st.core.fa.results = [(.a, .ok "a(b(absent))")] ∧ st.core.fb.results = [(.b, .cyc .a)] := by
  decide +kernel

/-- Waiting instead deadlocks: both blocked for the rest of the run. -/
theorem peekForce_wait_deadlock :
    let st := runSched peekForceP (cfgP .wait false) [.a] [.b] 30 [.run .a, .run .b]
    st.idle = false ∧ st.core.fa.results = [] ∧ st.core.fb.results = [] := by
  decide +kernel

/-- **The remedy gives a sequential answer on every schedule.** A peek whose wait would close a
cycle takes the absent path, and a force whose wait would close a cycle through the other's peek
waits for it to: on all 64 schedules both finish, with the answer of the sequential run from `a`'s
side or, when the second forcer runs alone first, from `b`'s side (its own self cycle). Never an
answer neither order gives, and `b` is `b(absent)` whenever it is stored. -/
theorem peekForce_yield_sequential :
    ∀ s ∈ scheds 6,
      let st := runSched peekForceP (cfgP .report true) [.a] [.b] 30 s
      st.idle = true ∧ st.core.fa.results = [(.a, .ok "a(b(absent))")] ∧
        (st.core.fb.results = [(.b, .ok "b(absent)")] ∨ st.core.fb.results = [(.b, .cyc .b)]) ∧
        st.read [.a, .b] = [some "a(b(absent))", some "b(absent)"] := by
  decide +kernel

/-! `Interrupt.peekBoth`: `a` peeks `b` and `b` peeks `a`. Sequentially neither order reports a
cycle (`forcePeek_memoizes_order`: the stored values differ by order, Track L's finding). -/

/-- Roots are facts, over `Interrupt.P2`. -/
def cfgB (pol : CyclePolicy) (yields : Bool) : Cfg Interrupt.P2 String Interrupt.P2 :=
  ⟨id, .own, pol, yields, true, "absent"⟩

/-- **Sequentially no order reports a cycle** on the mutual peek. -/
theorem peekBoth_sequential :
    (forcePeekAll Interrupt.peekBoth "absent" 9 [.a, .b] (fun _ => none)).1 = [.ok "a(b(absent))", .ok "b(absent)"] ∧
    (forcePeekAll Interrupt.peekBoth "absent" 9 [.b, .a] (fun _ => none)).1 = [.ok "b(a(absent))", .ok "a(absent)"] := by
  decide

/-- **The hypothesis for I68, confirmed on this shape: a wait-for cycle where no sequential order
reports a cycle.** Each forcer enters its fact and peeks the other's, in progress on the other
forcer: under §4.1 the peek waits, the second wait closes a wait-for cycle on facts, and `report`
raises a `.cyc` at `b` in the first forcer; the second then completes both facts from its side. -/
theorem peekBoth_report_false_cycle :
    let st := runSched Interrupt.peekBoth (cfgB .report false) [.a] [.b] 30 [.run .a, .run .b, .run .a, .run .b]
    st.idle = true ∧ st.core.fa.results = [(.a, .cyc .b)] ∧ st.core.fb.results = [(.b, .ok "b(a(absent))")] ∧
      st.read [.a, .b] = [some "a(absent)", some "b(a(absent))"] := by
  decide +kernel

/-- Waiting instead deadlocks. -/
theorem peekBoth_wait_deadlock :
    let st := runSched Interrupt.peekBoth (cfgB .wait false) [.a] [.b] 30 [.run .a, .run .b]
    st.idle = false ∧ st.core.fa.results = [] ∧ st.core.fb.results = [] := by
  decide +kernel

/-- **The remedy on the mutual peek: one of the two sequential answers on every schedule**, the
one from the side of the forcer that yields. Never a cycle, never a third answer. -/
theorem peekBoth_yield_sequential :
    ∀ s ∈ scheds 6,
      let st := runSched Interrupt.peekBoth (cfgB .report true) [.a] [.b] 30 s
      st.idle = true ∧
        ((st.core.fa.results = [(.a, .ok "a(b(absent))")] ∧ st.core.fb.results = [(.b, .ok "b(absent)")]) ∨
         (st.core.fa.results = [(.a, .ok "a(absent)")] ∧ st.core.fb.results = [(.b, .ok "b(a(absent))")])) := by
  decide +kernel

/-! ## 5. A root's scratch (rule 4 at root level)

A coarse root carries state beyond its facts' holes: a TASTy file's `treeAtAddr` map, into which
`TreeUnpickler.readIndexedDef` puts a `PoisonTree` sentinel before reading a definition and from
which it removes it after, with no `finally`. An owner that unwinds inside the root (the victim of
a cycle, a cancellation) leaves the sentinel; the waiter that takes the root over finds it and
asserts "Cyclic reference while unpickling". This is the design's rule 4 (an unwound completion
leaves the fact as it found it) violated at root level, the coarse-root form of
`Concurrent.abort_keep_hole_waiter_stuck`: there the hole was left set and the waiter waited for
ever; here the hole is released but the scratch is not, and the waiter fails. -/

/-- The chain `a → b → c → d` under one root (a file), with or without a `finally`. -/
def cfgC (scrub : Bool) : Cfg Chain String Unit := ⟨fun _ => (), .own, .report, false, scrub, "absent"⟩

/-- **A waiter taking over a poisoned root reports a false cycle.** Both forcers demand `a`; the
first enters `a` then `b` and is aborted; the second, which was waiting on the root, takes it over
and meets the sentinel at `a`: a `.cyc` with nothing cyclic in the rules. -/
theorem poison_waiter_false_cycle :
    let st := runSched chainP (cfgC false) [.a] [.a] 30 [.run .a, .run .a, .run .b, .abort .a]
    st.idle = true ∧ st.core.fb.results = [(.a, .cyc .a)] ∧ st.read [.a, .b, .c, .d] = [none, none, none, none] := by
  decide +kernel

/-- **With the scratch scrubbed on unwinding, the waiter takes over**, as in
`Concurrent.abort_waiter_takes_over`: the second forcer answers `a` and the store holds the chain. -/
theorem scrub_waiter_takes_over :
    let st := runSched chainP (cfgC true) [.a] [.a] 30 [.run .a, .run .a, .run .b, .abort .a]
    st.idle = true ∧ st.core.fb.results = [(.a, .ok "a(b(c(d)))")] ∧
      st.read [.a, .b, .c, .d] = [some "a(b(c(d)))", some "b(c(d))", some "c(d)", some "d"] := by
  decide +kernel

end Query.Roots
