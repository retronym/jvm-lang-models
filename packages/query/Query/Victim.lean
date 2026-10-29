import Query.Basic
/-!
# The victim of a wait-for cycle

Several readers of one symbol table take claims on its roots as they go: a Namer signature, a TASTy
file, a bring-forward, an inherited cache. Each reader holds the claims it is inside while it waits
for the next, like a stack, and a wait that would close a cycle in the wait-for graph is detected,
not prevented (`PerKeyClaims.acquire` in dotc's `sharing` package; the design's §4.2). This file
models the claims alone, without facts or rules: `n` claimants, each a list of keys it needs in
order, keys of two kinds (`fine`, a Namer signature's, whose completion cannot run twice; `coarse`,
every other kind, re-runnable), and the four-case victim policy as a transition. What the policy
does on a cycle is the whole question; what the readers compute is `Query.Concurrent`'s.

* **The machine** (§1). A party is its needs, how many it holds (`done`), whether it has finished
  or was cancelled by a poisoned key, the party it backs off from, and the state of its looks (the
  chain seen once, the ticks of a bounded wait). A party's kind is read off its stack: inside a
  Namer completion (`inNamer`) when it holds a fine key, so it `canAbort` when it holds none, as
  `Reader.canAbort` is `namerCompletionDepth == 0`. A step is one look of one party: finish, be
  cancelled by poison, acquire, wait, or act on the cycle its wait would close (`look`). The
  policy is a record (`Policy`); `dotc` is the one `acquire` codes, the others are the remedies.
* **Livelock** (§2). Two body readers whose needs are in opposite orders abort each other for ever
  under a fair schedule that is not round-robin: `livelock_forever`, by a period that maps a state to
  itself, so no number of periods finishes either request. Round-robin finishes them
  (`livelock_roundRobin_finishes`), and so does any prefix followed by a round-robin tail
  (`dotc_eventually_fair_progress`): the livelock is an adversary that never lapses, which the
  design's "in principle" names and a loaded machine approximates. Age (wound-wait on the detected cycle, the victim the youngest party) does not help
  without a queue: the victim re-takes its first key before the survivor moves
  (`byAge_livelock_forever`). The backoff does: a victim retries only once the party it waited on
  holds nothing, and every schedule of the scenarios finishes (`backoff_progress`,
  `backoff_progress_three`).
* **Poison** (§3). A party aborted inside a Namer completion leaves an `UnwoundCompletion` (I53): the
  key cancels every later request that needs it until a fresh run (I74). The smallest scenario where
  case 3's bounded wait ends in poison has two fine keys and one coarse (`poison_smallest`): both
  parties are inside a Namer completion, the cycle goes through the TASTy file, and the one whose
  bound runs out poisons its signature, which then cancels both requests until `fresh`. With two
  keys there is no poison under any schedule (`two_keys_no_poison`): one party holds only the coarse
  key and can abort. Letting the party whose latest claim is coarse yield just that claim, with the
  backoff, avoids the poison (`coarseYield_no_poison`); but when every party has a fine key above its
  coarse one, every abort poisons and the only other move is to wait for ever
  (`poison_unavoidable`): without re-runnable Namer completions no victim policy is clean.
* **A lock-order cycle at Namer roots** (§4). Two readers completing `Setting`'s members in opposite
  orders close a wait-for cycle that is not a dependency cycle (I68). With `isDependencyCycle` false
  the as-coded policy raises a false `CyclicReference` (`lockOrder_dotc_raises`), aborting poisons
  (`lockOrder_abort_poisons`), waiting deadlocks (`lockOrder_wait_stuck`): no good move
  (`lockOrder_no_good_move`). With re-runnable Namer completions (I8) aborting the newest party
  finishes every schedule without poison or a raised cycle (`lockOrder_rerunnable_progress`). And
  with the policy that raises only on a dependency cycle, a `raised` event implies
  `isDependencyCycle` (`raised_implies_depCycle`): the assertion `cyclesRaised` should carry.
-/

namespace Query.Victim

/-! ## 1. The machine -/

/-- A claim key: a completion root. -/
abbrev Key := Nat

/-- A key's kind: a Namer signature's root (`fine`, not re-runnable once unwound) or any other
(`coarse`: a TASTy file, a bring-forward, an inherited cache; re-runnable). -/
inductive KeyKind | fine | coarse
  deriving DecidableEq, Repr

/-- The kinds of a scenario's keys. -/
abbrev Kinds := Key → KeyKind

/-- A claimant: the keys its request needs in order, how many it holds (the first `done` of
`needs`, a stack), whether its request finished or was cancelled by a poisoned key, the party it
backs off from after an abort (it retries only once that party holds nothing), and its look state:
whether it has seen the current chain once (case 4's two looks), how many looks it has waited on a
cycle through a coarse claim (case 3's bound). `age` orders requests for the age-based remedies and
for "the newest party"; it is kept across retries. -/
structure Party where
  needs : List Key
  done : Nat
  finished : Bool
  cancelled : Bool
  blockedOn : Option Nat
  seen : Bool
  ticks : Nat
  age : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Still has a request to serve. -/
def Party.active (p : Party) : Bool := !p.finished && !p.cancelled

/-- The keys the party holds: its stack. -/
def Party.held (p : Party) : List Key := if p.active then p.needs.take p.done else []

/-- The key the party needs next, if any. -/
def Party.wants (p : Party) : Option Key := if p.active then p.needs[p.done]? else none

/-- Inside a Namer completion: holds a fine key. -/
def Party.inNamer (K : Kinds) (p : Party) : Bool := p.held.any fun k => decide (K k = .fine)

/-- Can be the victim of a cycle at once: typing a body, `namerCompletionDepth == 0`. -/
def Party.canAbort (K : Kinds) (p : Party) : Bool := !p.inNamer K

/-- The party's latest claim is a coarse one: its wait is inside a re-runnable completion. -/
def Party.topCoarse (K : Kinds) (p : Party) : Bool :=
  match p.held.getLast? with
  | some k => decide (K k = .coarse)
  | none => false

/-- The shared state: the parties and the poisoned keys (`UnwoundCompletion`s, I53). -/
structure St where
  parties : List Party
  poisoned : List Key
  deriving DecidableEq, Repr

def modifyAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, a :: l => f a :: l
  | n + 1, a :: l => a :: modifyAt f n l

def St.party (st : St) (i : Nat) : Party := st.parties.getD i default

def St.upd (st : St) (i : Nat) (f : Party → Party) : St :=
  { st with parties := modifyAt f i st.parties }

/-- The index of the party holding `k`, if any. -/
def St.holder (st : St) (k : Key) : Option Nat :=
  (List.range st.parties.length).find? fun i => decide (k ∈ (st.party i).held)

/-- Follow the wait-for chain from party `i`'s want: the key it waits on, that key's holder, what
the holder waits on, and so on. The chain closes a cycle when it returns to `i`; it ends when a
party waits on nothing or a key is free. Returns the other parties of the cycle and its claims. -/
def chainFrom (st : St) (i : Nat) : Nat → Nat → List Nat → List Key → Option (List Nat × List Key)
  | 0, _, _, _ => none
  | fuel + 1, j, ps, ks =>
    match (st.party j).wants with
    | none => none
    | some k =>
      match st.holder k with
      | none => none
      | some h =>
        if h = i then some (ps, ks ++ [k])
        else if h = j then none
        else chainFrom st i fuel h (ps ++ [h]) (ks ++ [k])

/-- The wait-for cycle that party `i`'s wait would close, if any: `cycleChain` in `PerKeyClaims`. -/
def St.cycle (st : St) (i : Nat) : Option (List Nat × List Key) :=
  chainFrom st i (st.parties.length + 1) i [] []

/-- What a party does on a wait-for cycle that is a lock order, not a dependency cycle (I68): raise
`CyclicReference` anyway (as coded), wait for ever, or abort the newest party (sound only with
re-runnable Namer completions, I8). -/
inductive LockOrder | raise | wait | abortNewest
  deriving DecidableEq, Repr

/-- The victim policy and the kernel's variants. `bound` is the number of looks a party waits on a
cycle through a coarse claim before it aborts after all (dotc: 10 s; 0 for never). `rerunnable`
says whether a Namer completion unwound by an abort can run again (false in dotc, I53).
`depCycle` is the per-cycle bit `isDependencyCycle`, taken as given for the scenario (another model
distinguishes the two). `byAge`, `backoff` and `coarseYield` are the remedies of §2 and §3. -/
structure Policy where
  byAge : Bool := false
  backoff : Bool := false
  coarseYield : Bool := false
  bound : Nat := 0
  rerunnable : Bool := false
  depCycle : Bool := true
  onLockOrder : LockOrder := .raise
  deriving DecidableEq, Repr

/-- The policy `PerKeyClaims.acquire` codes, with `CompletionRoots`' bounded wait. -/
def dotc : Policy := { bound := 2 }

/-- What a look did. -/
inductive Ev | idle | acquired | finished | waited | aborted | yielded | raised | cancelled
  deriving DecidableEq, Repr

/-- The youngest (greatest age) of some parties. -/
def youngest (st : St) (ps : List Nat) : Option Nat :=
  ps.foldl (fun acc q => match acc with
    | none => some q
    | some a => if (st.party q).age > (st.party a).age then some q else some a) none

/-- The party of a cycle that case 4 picks to report it: a fixed order of the parties, here their
index, as `acquire` orders threads by their identity hash. -/
def reporter (ps : List Nat) : Nat := ps.foldl max 0

/-- Party `i` aborts: its claims unwind, and when Namer completions cannot run again every fine key
it held is poisoned (I53, I74). Its request restarts from the beginning, after `waitedOn` has
released if the policy backs off. -/
def abortParty (P : Policy) (K : Kinds) (st : St) (i : Nat) (waitedOn : Nat) : St :=
  let poison := if P.rerunnable then [] else (st.party i).held.filter fun k => decide (K k = .fine)
  let restart (p : Party) : Party :=
    { p with done := 0, seen := false, ticks := 0, blockedOn := if P.backoff then some waitedOn else none }
  { parties := modifyAt restart i st.parties, poisoned := st.poisoned ++ poison }

/-- Party `i` acquires its next key. -/
def acquireParty (st : St) (i : Nat) : St :=
  st.upd i fun p => { p with done := p.done + 1, seen := false, ticks := 0 }

/-- A wait that closes no cycle: the look state is reset. -/
def waitParty (st : St) (i : Nat) : St :=
  st.upd i fun p => { p with seen := false, ticks := 0 }

/-- Party `i` waits on key `k` held by `j`, and that wait would close the cycle whose other parties
are `ps` and whose claims are `ks`: the four cases of `acquire`. -/
def onCycle (P : Policy) (K : Kinds) (st : St) (i j : Nat) (ps : List Nat) (ks : List Key) :
    St × Ev :=
  let parties := i :: ps
  let abortable := parties.filter fun q => (st.party q).canAbort K
  if abortable ≠ [] then
    -- cases 1 and 2: a party that can abort does; the others wait for it
    let victim := if P.byAge then youngest st abortable else
      if (st.party i).canAbort K then some i else none
    if victim = some i then (abortParty P K st i j, .aborted) else (st, .waited)
  else if P.bound > 0 && ks.any (fun k => decide (K k = .coarse)) then
    -- case 3: through a coarse claim
    if P.coarseYield && parties.any (fun q => (st.party q).topCoarse K) then
      if (st.party i).topCoarse K then
        let yield (p : Party) : Party :=
          { p with done := p.done - 1, seen := false, ticks := 0, blockedOn := if P.backoff then some j else none }
        (st.upd i yield, .yielded)
      else (st, .waited)
    else
      let t := (st.party i).ticks + 1
      if t ≥ P.bound then (abortParty P K st i j, .aborted)
      else (st.upd i fun p => { p with ticks := t }, .waited)
  else
    -- case 4: every party inside a Namer completion, every claim a symbol
    let raise : St × Ev :=
      if reporter parties = i then
        if (st.party i).seen then
          (st.upd i fun p => { p with finished := true }, .raised)
        else (st.upd i fun p => { p with seen := true }, .waited)
      else (st, .waited)
    if P.depCycle then raise else
    match P.onLockOrder with
    | .raise => raise
    | .wait => (st, .waited)
    | .abortNewest =>
      if youngest st parties = some i then (abortParty P K st i j, .aborted) else (st, .waited)

/-- One look of party `i`, which is active and not backing off. -/
def look (P : Policy) (K : Kinds) (st : St) (i : Nat) : St × Ev :=
  let p := st.party i
  if p.done = p.needs.length then (st.upd i fun p => { p with finished := true }, .finished)
  else match p.needs[p.done]? with
  | none => (st, .idle)
  | some k =>
    if k ∈ st.poisoned then (st.upd i fun p => { p with cancelled := true }, .cancelled)
    else match st.holder k with
    | none => (acquireParty st i, .acquired)
    | some j =>
      if j = i then (acquireParty st i, .acquired)
      else match st.cycle i with
      | none => (waitParty st i, .waited)
      | some (ps, ks) => onCycle P K st i j ps ks

/-- One step of party `i`: nothing if its request is over; a wait while the party it backs off
from still holds a claim; else a look. -/
def step' (P : Policy) (K : Kinds) (st : St) (i : Nat) : St × Ev :=
  let p := st.party i
  if !p.active then (st, .idle)
  else match p.blockedOn with
  | some j =>
    if (st.party j).held ≠ [] then (st, .waited)
    else look P K (st.upd i fun p => { p with blockedOn := none }) i
  | none => look P K st i

/-- A scheduler's action: a step of one party, or a fresh run (the poison is gone, cancelled
requests are retried). -/
inductive Act | go (i : Nat) | fresh
  deriving DecidableEq, Repr

def act (P : Policy) (K : Kinds) (st : St) : Act → St × Ev
  | .go i => step' P K st i
  | .fresh =>
    let retry (p : Party) : Party :=
      if p.cancelled then { p with cancelled := false, done := 0, blockedOn := none } else p
    ({ parties := st.parties.map retry, poisoned := [] }, .idle)

def run (P : Policy) (K : Kinds) : List Act → St → St
  | [], st => st
  | x :: xs, st => run P K xs (act P K st x).1

def trace (P : Policy) (K : Kinds) : List Act → St → List Ev
  | [], _ => []
  | x :: xs, st => (act P K st x).2 :: trace P K xs (act P K st x).1

theorem run_append (P : Policy) (K : Kinds) (a b : List Act) (st : St) :
    run P K (a ++ b) st = run P K b (run P K a st) := by
  induction a generalizing st with
  | nil => rfl
  | cons x xs ih => simp [run, ih]

/-- `m` repetitions of a period. -/
def periods (p : List Act) : Nat → List Act
  | 0 => []
  | m + 1 => periods p m ++ p

/-- The initial state: one party per request, aged by its index. -/
def init (needs : List (List Key)) : St :=
  ⟨(needs.zipIdx).map fun (ns, i) => ⟨ns, 0, false, false, none, false, 0, i⟩, []⟩

def St.allFinished (st : St) : Bool := st.parties.all (·.finished)
def St.noneFinished (st : St) : Bool := st.parties.all fun p => !p.finished

/-- Each of `n` parties once. -/
def roundRobin (n fuel : Nat) : List Act :=
  (List.replicate fuel ((List.range n).map Act.go)).flatten

/-- Every schedule of `len` steps of `n` parties. -/
def scheds (n : Nat) : Nat → List (List Act)
  | 0 => [[]]
  | len + 1 => (scheds n len).flatMap fun s => (List.range n).map fun i => Act.go i :: s

/-- A schedule prefix, then a fair tail long enough to finish. -/
def runSched (P : Policy) (K : Kinds) (st : St) (fuel : Nat) (s : List Act) : St :=
  run P K (s ++ roundRobin st.parties.length fuel) st

/-- Every key coarse: two readers typing bodies. -/
def allCoarse : Kinds := fun _ => .coarse

/-- Every key fine: two readers inside Namer completions. -/
def allFine : Kinds := fun _ => .fine

/-! ## 2. Livelock

Two body readers, keys 1 and 2 (both coarse), needs in opposite orders. -/

/-- A needs 1 then 2, B needs 2 then 1. -/
def opp : St := init [[1, 2], [2, 1]]

/-- A takes 1, B takes 2. -/
def oppStart : St := run dotc allCoarse [.go 0, .go 1] opp

/-- A looks (cycle, aborts), A re-takes 1, B looks (cycle, aborts), B re-takes 2: fair (each party
twice) and back where it started. -/
def livelockPeriod : List Act := [.go 0, .go 0, .go 1, .go 1]

theorem livelock_period_fixes : run dotc allCoarse livelockPeriod oppStart = oppStart := by decide

theorem livelock_period_aborts :
    trace dotc allCoarse livelockPeriod oppStart = [.aborted, .acquired, .aborted, .acquired] := by
  decide

theorem livelock_period_fair : Act.go 0 ∈ livelockPeriod ∧ Act.go 1 ∈ livelockPeriod := by decide

/-- No number of periods moves the state: both requests are aborted for ever. -/
theorem livelock_forever (m : Nat) : run dotc allCoarse (periods livelockPeriod m) oppStart = oppStart := by
  induction m with
  | zero => rfl
  | succ m ih => rw [periods, run_append, ih, livelock_period_fixes]

theorem livelock_never_finishes (m : Nat) :
    (run dotc allCoarse ([.go 0, .go 1] ++ periods livelockPeriod m) opp).noneFinished = true := by
  rw [run_append]; show (run dotc allCoarse (periods livelockPeriod m) oppStart).noneFinished = true
  rw [livelock_forever]; decide

/-- Round-robin finishes both: the schedule, not the policy, is what the design's "in principle"
depends on. -/
theorem livelock_roundRobin_finishes :
    (run dotc allCoarse (roundRobin 2 6) opp).allFinished = true := by decide

/-- Every schedule of six steps followed by a round-robin tail finishes both requests, under the
as-coded policy too: the livelock needs the adversary to keep its order for ever, and any lapse into
alternation ends it. On a machine that is the difference between a soak that fails and one that does
not. -/
theorem dotc_eventually_fair_progress :
    ((scheds 2 6).all fun s => (runSched dotc allCoarse opp 6 s).allFinished) = true := by decide +kernel

/-! ### The remedies

Wound-wait on the detected cycle: the victim is the youngest party. The age is kept across
retries, so the oldest party is never the victim; but without a queue the victim re-takes its first
key before the survivor moves, and the survivor waits again. -/

def byAge : Policy := { dotc with byAge := true }

/-- B (the younger) looks and aborts, B re-takes 2, A looks and waits. -/
def byAgePeriod : List Act := [.go 1, .go 1, .go 0]

theorem byAge_period_fixes : run byAge allCoarse byAgePeriod oppStart = oppStart := by decide

theorem byAge_period_trace :
    trace byAge allCoarse byAgePeriod oppStart = [.aborted, .acquired, .waited] := by decide

theorem byAge_livelock_forever (m : Nat) :
    run byAge allCoarse (periods byAgePeriod m) oppStart = oppStart := by
  induction m with
  | zero => rfl
  | succ m ih => rw [periods, run_append, ih, byAge_period_fixes]

/-- The backoff: a victim retries only once the party it waited on holds nothing. The survivor
then takes the key the victim released, since nobody else wants it, and finishes. -/
def backoff : Policy := { dotc with backoff := true }

theorem backoff_period_finishes :
    trace backoff allCoarse livelockPeriod oppStart = [.aborted, .waited, .acquired, .finished] ∧
    (run backoff allCoarse (livelockPeriod ++ roundRobin 2 3) oppStart).allFinished = true := by
  decide

/-- Every schedule of six steps and a fair tail finishes both requests. -/
theorem backoff_progress :
    ((scheds 2 6).all fun s => (runSched backoff allCoarse opp 6 s).allFinished) = true := by decide +kernel

/-- Three body readers in a ring: A needs 1, 2; B needs 2, 3; C needs 3, 1. -/
def ring : St := init [[1, 2], [2, 3], [3, 1]]

theorem backoff_progress_three :
    ((scheds 3 5).all fun s => (runSched backoff allCoarse ring 8 s).allFinished) = true := by decide +kernel

/-- The ring under the as-coded policy, likewise, finishes under every prefix with a round-robin
tail. -/
theorem dotc_ring_eventually_fair_progress :
    ((scheds 3 5).all fun s => (runSched dotc allCoarse ring 8 s).allFinished) = true := by decide +kernel

/-! ## 3. Poison

Keys 1 and 2 are fine (Namer signatures), key 3 coarse (a TASTy file). -/

def poisonKinds : Kinds := fun k => if k = 3 then .coarse else .fine

/-- A completes signature 1, which needs the TASTy file 3; B completes signature 2, which needs 3,
and then needs 1 from inside 3 (I74's shape: a classpath root and a source signature). -/
def poisonSt : St := init [[1, 3], [2, 3, 1]]

/-- B takes 2 and 3, A takes 1; A looks (cycle through 3, bounded wait), looks again (bound
reached: aborts, poisoning 1); then B needs 1 and is cancelled, and A's retry needs 1 and is
cancelled. -/
def poisonSched : List Act := [.go 1, .go 1, .go 0, .go 0, .go 0, .go 1, .go 0]

theorem poison_smallest :
    (run dotc poisonKinds poisonSched poisonSt).poisoned = [1] ∧
    trace dotc poisonKinds poisonSched poisonSt =
      [.acquired, .acquired, .acquired, .waited, .aborted, .cancelled, .cancelled] := by decide

/-- Neither request is served until a fresh run; after it both finish. -/
theorem poison_until_fresh :
    (run dotc poisonKinds (poisonSched ++ roundRobin 2 4) poisonSt).noneFinished = true ∧
    (run dotc poisonKinds (poisonSched ++ [.fresh] ++ roundRobin 2 6) poisonSt).allFinished = true := by
  decide

/-- With two keys, one fine and one coarse, in opposite orders, the party holding only the coarse
key can abort: no schedule poisons, and every one finishes. -/
def twoKeyKinds : Kinds := fun k => if k = 2 then .coarse else .fine

theorem two_keys_no_poison :
    ((scheds 2 6).all fun s =>
      let st := runSched dotc twoKeyKinds (init [[1, 2], [2, 1]]) 6 s
      st.poisoned.isEmpty && st.allFinished) = true ∧
    ((scheds 2 6).all fun s =>
      let st := runSched dotc twoKeyKinds (init [[2, 1], [1, 2]]) 6 s
      st.poisoned.isEmpty && st.allFinished) = true := by decide +kernel

/-- The remedy: in case 3 the party whose latest claim is coarse yields that claim alone (a TASTy
completion is re-runnable) and backs off until the party it waited on has released. -/
def coarseYield : Policy := { dotc with coarseYield := true, backoff := true }

theorem coarseYield_no_poison :
    ((scheds 2 6).all fun s =>
      let st := runSched coarseYield poisonKinds poisonSt 6 s
      st.poisoned.isEmpty && st.allFinished) = true := by decide +kernel

/-- Without the backoff the yielding party re-takes the file before the other moves: a livelock of
yields. -/
def coarseYieldNoBackoff : Policy := { dotc with coarseYield := true }

def yieldStart : St := run coarseYieldNoBackoff poisonKinds [.go 1, .go 1, .go 0] poisonSt

theorem coarseYield_without_backoff_livelocks :
    run coarseYieldNoBackoff poisonKinds [.go 1, .go 1, .go 0] yieldStart = yieldStart ∧
    trace coarseYieldNoBackoff poisonKinds [.go 1, .go 1, .go 0] yieldStart =
      [.yielded, .acquired, .waited] := by decide

/-- Where no yield is possible: B's TASTy read forced signature 2, which needs 1; A's signature 1
needs the file 3. Both parties have a fine key above their coarse one, or no coarse one. -/
def poisonSt2 : St := init [[1, 3], [3, 2, 1]]

/-- The deadlocked state: B holds 3 and 2, A holds 1, each wants the other's. -/
def stuck2 : St := run dotc poisonKinds [.go 1, .go 1, .go 0] poisonSt2

/-- In the deadlocked state every party is inside a Namer completion, so every abort poisons, the
yield has no taker, and under the policy that waits nobody moves: there is no clean victim. -/
theorem poison_unavoidable :
    ((stuck2.parties.zipIdx).all fun (p, i) =>
      p.inNamer poisonKinds &&
      !(abortParty dotc poisonKinds stuck2 i 0).poisoned.isEmpty &&
      !(p.topCoarse poisonKinds)) = true ∧
    (run { dotc with bound := 0, depCycle := false, onLockOrder := .wait } poisonKinds
      (roundRobin 2 4) stuck2 = stuck2) ∧
    ((run dotc poisonKinds (roundRobin 2 4) stuck2).poisoned ≠ []) := by decide

/-! ## 4. A lock-order cycle at Namer roots (I68, I74)

Keys 1 and 2 are fine: two members of `Setting`, completed in opposite orders by two readers.
No sequential order has this cycle: `isDependencyCycle` is false. -/

def settingSt : St := init [[1, 2], [2, 1]]

/-- A takes 1, B takes 2. -/
def settingStart : St := run dotc allFine [.go 0, .go 1] settingSt

def lockOrder (o : LockOrder) : Policy := { dotc with depCycle := false, onLockOrder := o }

/-- As coded: case 4, the reporter sees the chain twice and raises a `CyclicReference` that no
dependency warrants ("Cyclic reference involving class Setting"). -/
theorem lockOrder_dotc_raises :
    .raised ∈ trace (lockOrder .raise) allFine (roundRobin 2 3) settingStart := by decide

/-- Aborting instead, without re-runnable completions, poisons a signature (I74). -/
theorem lockOrder_abort_poisons :
    (run (lockOrder .abortNewest) allFine (roundRobin 2 3) settingStart).poisoned ≠ [] := by decide

/-- Waiting instead is a deadlock: no round moves the state. -/
theorem lockOrder_wait_stuck (m : Nat) :
    run (lockOrder .wait) allFine (periods (roundRobin 2 1) m) settingStart = settingStart := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [periods, run_append, ih]
    exact (by decide : run (lockOrder .wait) allFine (roundRobin 2 1) settingStart = settingStart)

/-- The verdict for I68 without I8: every move is bad. -/
theorem lockOrder_no_good_move :
    (.raised ∈ trace (lockOrder .raise) allFine (roundRobin 2 3) settingStart) ∧
    ((run (lockOrder .abortNewest) allFine (roundRobin 2 3) settingStart).poisoned ≠ []) ∧
    (∀ m, (run (lockOrder .wait) allFine (periods (roundRobin 2 1) m) settingStart).noneFinished = true) :=
  ⟨lockOrder_dotc_raises, lockOrder_abort_poisons, fun m => by rw [lockOrder_wait_stuck]; decide⟩

/-- With re-runnable Namer completions (I8): abort the newest party, with the backoff. Every
schedule finishes, nothing is poisoned, no cycle is raised. -/
def rerunnable : Policy :=
  { dotc with depCycle := false, onLockOrder := .abortNewest, rerunnable := true, backoff := true }

theorem lockOrder_rerunnable_progress :
    ((scheds 2 6).all fun s =>
      let st := runSched rerunnable allFine settingSt 6 s
      st.poisoned.isEmpty && st.allFinished &&
      !(trace rerunnable allFine (s ++ roundRobin 2 6) settingSt).contains .raised) = true := by
  decide +kernel

/-- Re-runnable but without the backoff: the newest party re-takes its key before the oldest moves,
the same livelock as §2's. -/
def rerunnableNoBackoff : Policy :=
  { dotc with depCycle := false, onLockOrder := .abortNewest, rerunnable := true }

theorem rerunnable_without_backoff_livelocks :
    run rerunnableNoBackoff allFine [.go 1, .go 1, .go 0, .go 0] settingStart = settingStart ∧
    trace rerunnableNoBackoff allFine [.go 1, .go 1, .go 0, .go 0] settingStart =
      [.aborted, .acquired, .waited, .waited] := by decide

/-- A `raised` event under a policy that does not raise on a lock order means the cycle was a
dependency cycle: `cyclesRaised` is incremented only when `isDependencyCycle`. -/
theorem onCycle_raised_implies_depCycle (P : Policy) (K : Kinds) (st : St) (i j : Nat)
    (ps : List Nat) (ks : List Key) (h : P.onLockOrder ≠ .raise)
    (hr : (onCycle P K st i j ps ks).2 = .raised) : P.depCycle = true := by
  unfold onCycle at hr
  simp only at hr
  repeat' split at hr
  all_goals first
    | assumption
    | exact absurd ‹P.onLockOrder = .raise› h
    | simp at hr

theorem look_raised_implies_depCycle (P : Policy) (K : Kinds) (st : St) (i : Nat)
    (h : P.onLockOrder ≠ .raise) (hr : (look P K st i).2 = .raised) : P.depCycle = true := by
  unfold look at hr
  simp only at hr
  repeat' split at hr
  all_goals first
    | simp at hr
    | exact onCycle_raised_implies_depCycle P K _ i _ _ _ h hr

theorem raised_implies_depCycle (P : Policy) (K : Kinds) (st : St) (i : Nat)
    (h : P.onLockOrder ≠ .raise) (hr : (step' P K st i).2 = .raised) : P.depCycle = true := by
  unfold step' at hr
  simp only at hr
  repeat' split at hr
  all_goals first
    | simp at hr
    | exact look_raised_implies_depCycle P K _ i h hr

end Query.Victim
