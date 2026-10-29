import Query.Basic
/-!
# The wait-for graph read one edge at a time

`PerKeyClaims` (retronym/scala3#84, `dotty.tools.sharing`) is a claim per key: `acquire` waits on the
holder's latch, and before each slice of the wait it walks the wait-for graph (`cycleChain`): the
claim it wants, what that claim's owner waits on (`Claimant.waitingOn`), and so on, until it meets a
claim of its own. The graph is read from fields the other claimants change as they go, one edge at a
time and with no snapshot, so a chain is a set of edges seen at *different* instants. Two false cycles
came from that (I87, released claims still named by woken waiters; I98, a claim released after it was
read whose owner then waited on the walker), and §8 of `interactive-multi-reader.md` says a second
source of false cycles besides I87's remains unfound.

This module is a small operational model of the walk, written off `PerKeyClaims.acquire`, `release`
and `cycleChain`, with the registry and the latch kept apart (release is `claims.remove` *then*
`countDown`), the walker's reads as events interleaved with the other claimants' steps, and the
ground truth as a cycle of the key-level wait-for graph at one instant.

* **The model** (§1). Claimants, keys, claim objects with identities, the registry, the latches, each
  claimant's `waitingOn` and the key it is inside `acquire` of; the events of the other claimants and
  the walker's reads, exactly in the order `cycleChain` makes them.
* **Ground truth** (§2). `realCycle`: at one instant, following "is inside `acquire(k)`" and "`k`'s
  registered claim is held by" from the walker leads back to the walker.
* **The two findings reconstructed** (§3). With neither check, I87's history gives a chain and no
  instant has a cycle (`i87_false_chain`); with the entry check but not the final one, I98's does
  (`i98_false_chain`). The final all-held check subsumes the entry check (`entry_check_subsumed`).
* **What remains with both** (§4). `release_window_false_chain`: a chain whose waits never coexisted,
  through a claim whose owner has left its wait by unwinding (an abort, a `cycle()` raise, an
  interrupt) and not yet counted down. Over the enumerated spaces every such chain has an unwind in it
  (`false_chain_needs_unwind`): the walk is sound while nobody unwinds. Counting down before removing,
  or asking the registry, closes the window between `remove` and `countDown` but not the one between
  the throw and the release (`cd_first_not_enough`); re-reading the edges at the end, or a sequence
  number that says nothing changed, is sound on the space (`edge_check_sound`, `snapshot_sound`).
* **Two looks and the first look** (§5). Two consecutive looks that return the same chain imply a
  cycle real at some instant (`two_looks_real`), so the two-looks rule is sound on the space; a
  claimant that aborts at its first look can still be aborted by the false chain of §4
  (`first_look_false_abort`).

No Mathlib, no `native_decide` outside `example`s; the theorems over a space are `decide` on every
interleaving the space names, and the file says so where a claim is checked on a space and not proved
for every history.
-/

namespace Query.WaitGraph

/-! ## 1. The model -/

/-- A claimant: `Claimant` in the real system, one per thread. `0` is the walker throughout. -/
abbrev Who := Nat

/-- A key of the registry. -/
abbrev Key := Nat

/-- The identity of a claim object: its index in `St.claims`, which only grows, so a key acquired
again gets a new identity and `Claim.done` of the old one is a different latch. -/
abbrev ClaimId := Nat

/-- A claim object: `PerKeyClaims.Claim(owner, what, holds, done)` without `what`, and `holds` kept
at one (re-entrance by the owner never waits and never walks, so it does not matter here). -/
structure Claim where
  owner : Who
  key : Key
  deriving DecidableEq, Repr

/-- The shared state at one instant.

* `claims`: every claim object ever made, by identity.
* `reg`: the `ConcurrentHashMap`, a key and the claim registered for it.
* `down`: the claims whose `CountDownLatch` has counted down (`getCount == 0`).
* `waitingOn`: `Claimant.waitingOn`, a claimant and the claim it names; absent is `null`.
* `acquiring`: which claimants are inside `acquire(k)` and have not been granted it: the ground truth
  of "waits for `k`", which the field `waitingOn` only approximates (it is null between slices and
  stale after a wake).
* `unwound`: claimants that have thrown out of an `acquire` (an abort, a `cycle()` raise, an
  interrupt in `await`) and are unwinding: they release and then do nothing more in the model.
* `epoch`: a count of every change, for the snapshot design of §4. -/
structure St where
  claims : List Claim
  reg : List (Key × ClaimId)
  down : List ClaimId
  waitingOn : List (Who × ClaimId)
  acquiring : List (Who × Key)
  unwound : List Who
  epoch : Nat
  deriving DecidableEq, Repr

/-- Lookup in an association list. -/
def assoc {α β : Type} [DecidableEq α] (a : α) : List (α × β) → Option β
  | [] => none
  | (a', b) :: l => if a = a' then some b else assoc a l

/-- Remove a key from an association list. -/
def erase {α β : Type} [DecidableEq α] (a : α) : List (α × β) → List (α × β)
  | [] => []
  | (a', b) :: l => if a = a' then erase a l else (a', b) :: erase a l

namespace St

/-- The claim object of an identity. -/
def claim (s : St) (c : ClaimId) : Option Claim := s.claims[c]?

/-- The owner of a claim. -/
def owner (s : St) (c : ClaimId) : Option Who := (s.claim c).map (·.owner)

/-- The key of a claim. -/
def key (s : St) (c : ClaimId) : Option Key := (s.claim c).map (·.key)

/-- `c.done.getCount == 0`. -/
def isDown (s : St) (c : ClaimId) : Bool := s.down.contains c

/-- `claims.get(c.key) eq c`: the claim is the one registered for its key. -/
def inReg (s : St) (c : ClaimId) : Bool :=
  match s.key c with
  | some k => assoc k s.reg == some c
  | none => false

/-- Half released: removed and not counted down (the window of `release` as written), or counted down
and not removed (the window of the count-down-first order of §4). A fresh claim is registered and up;
a released one is unregistered and down. -/
def midRelease (s : St) (c : ClaimId) : Bool := s.inReg c == s.isDown c

/-- The claim identities so far. -/
def ids (s : St) : List ClaimId := List.range s.claims.length

/-- Is claimant `w` half way through a release, other than of `c`? Between the two steps of `release`
a thread does nothing else, so every other event of `w` waits for the second step. -/
def busyExcept (s : St) (w : Who) (c : Option ClaimId) : Bool :=
  s.ids.any fun c' => s.owner c' == some w && some c' != c && s.midRelease c'

/-- Is `w` half way through a release? -/
def busy (s : St) (w : Who) : Bool := s.busyExcept w none

/-- Does `w` hold a registered claim on `k`? -/
def holds (s : St) (w : Who) (k : Key) : Bool :=
  match assoc k s.reg with
  | some c => s.owner c == some w
  | none => false

/-- The walker's start: claimant `i` holds key `i` through claim `i`, for `i < n`; claimant `me` is
inside `acquire k0`. -/
def init (n : Nat) (me : Who) (k0 : Key) : St :=
  { claims := (List.range n).map fun i => ⟨i, i⟩
    reg := (List.range n).map fun i => (i, i)
    down := []
    waitingOn := []
    acquiring := [(me, k0)]
    unwound := []
    epoch := 0 }

end St

/-- Which order `release` takes, and which checks `cycleChain` makes.

* `i87`: stop at a claim whose latch has counted down (a stale edge of a woken waiter), the I87 fix.
* `i98`: return the chain only if every claim in it is still up after the walk, the I98 fix.
* `cdFirst`: `release` counts down before it removes, so that "up" implies "registered".
* `mapCheck`: the final check asks the registry (`claims.get(c.key) eq c`), not the latch.
* `edgeCheck`: the final check re-reads each edge (`waiter.waitingOn eq claim`) as well as each claim.
* `snapshot`: the chain is returned only if nothing changed since the walk's first read (a global
  sequence number read before and after, the seqlock shape). -/
structure Design where
  i87 : Bool
  i98 : Bool
  cdFirst : Bool := false
  mapCheck : Bool := false
  edgeCheck : Bool := false
  snapshot : Bool := false
  deriving DecidableEq, Repr

/-- `cycleChain` as first written: no check of the latches. -/
def Design.orig : Design := { i87 := false, i98 := false }

/-- The I87 fix alone: the entry check. -/
def Design.i87only : Design := { i87 := true, i98 := false }

/-- The I98 fix without the I87 entry check. -/
def Design.i98only : Design := { i87 := false, i98 := true }

/-- `PerKeyClaims.cycleChain` at retronym/scala3#84: both checks. -/
def Design.both : Design := { i87 := true, i98 := true }

/-- Both checks and `release` counting down before it removes. -/
def Design.withCdFirst : Design := { i87 := true, i98 := true, cdFirst := true }

/-- Both checks, the final one against the registry. -/
def Design.withMapCheck : Design := { i87 := true, i98 := true, mapCheck := true }

/-- Both checks, count-down-first, and the edges re-read at the end. -/
def Design.withEdgeCheck : Design := { i87 := true, i98 := true, cdFirst := true, edgeCheck := true }

/-- Both checks and a sequence number: the chain is kept only if nothing changed during the walk. -/
def Design.withSnapshot : Design := { i87 := true, i98 := true, snapshot := true }

/-- An event. The first seven are steps of claimants other than the walker; `read` is the walker's
next read of `cycleChain`; `look` is the walker's next slice (its `await` returned, it clears
`waitingOn`, re-reads the registry and walks again).

* `start w k`: `w` enters `acquire(k)`, finds it held, and is a waiter of `k` from here on.
* `wait w`: `w` runs `me.waitingOn = c` for the claim registered on its key, before `await`.
* `wake w`: `w`'s `await` returned (timeout or count-down) and its `finally` cleared `waitingOn`.
* `grant w`: `w` finds its key free and `putIfAbsent`s a new claim: a new identity.
* `unwind w`: `w` throws out of `acquire` (its own abort, a `cycle()` raise, an interrupt) with
  `waitingOn` already cleared by the `finally`, and will release what it holds.
* `remove c`: `claims.remove(key)` of `release`.
* `countDown c`: `c.done.countDown()` of `release`. -/
inductive Ev
  | start (w : Who) (k : Key)
  | wait (w : Who)
  | wake (w : Who)
  | grant (w : Who)
  | unwind (w : Who)
  | remove (c : ClaimId)
  | countDown (c : ClaimId)
  | read
  | look
  deriving DecidableEq, Repr

/-- The step of a claimant other than the walker, or `none` when the event is not enabled: the model
admits only histories every event of which the real code can take. -/
def bg (d : Design) (s : St) : Ev → Option St
  | .start w k =>
    if s.busy w || s.unwound.contains w || (assoc w s.acquiring).isSome || s.holds w k then none
    else some { s with acquiring := (w, k) :: s.acquiring, epoch := s.epoch + 1 }
  | .wait w =>
    match assoc w s.acquiring, assoc w s.waitingOn with
    | some k, none =>
      match assoc k s.reg with
      | some c => if s.busy w || s.owner c == some w then none
          else some { s with waitingOn := (w, c) :: s.waitingOn, epoch := s.epoch + 1 }
      | none => none
    | _, _ => none
  | .wake w =>
    if (assoc w s.waitingOn).isSome then
      some { s with waitingOn := erase w s.waitingOn, epoch := s.epoch + 1 }
    else none
  | .grant w =>
    match assoc w s.acquiring, assoc w s.waitingOn with
    | some k, none =>
      if s.busy w || (assoc k s.reg).isSome then none
      else some { s with claims := s.claims ++ [⟨w, k⟩], reg := (k, s.claims.length) :: s.reg,
                         acquiring := erase w s.acquiring, epoch := s.epoch + 1 }
    | _, _ => none
  | .unwind w =>
    match assoc w s.acquiring, assoc w s.waitingOn with
    | some _, none =>
      if s.busy w then none
      else some { s with acquiring := erase w s.acquiring, unwound := w :: s.unwound,
                         epoch := s.epoch + 1 }
    | _, _ => none
  | .remove c =>
    match s.claim c with
    | some cl =>
      if (assoc cl.owner s.acquiring).isSome || !s.inReg c || s.busyExcept cl.owner (some c)
          || (s.isDown c != d.cdFirst) then none
      else some { s with reg := erase cl.key s.reg, epoch := s.epoch + 1 }
    | none => none
  | .countDown c =>
    match s.claim c with
    | some cl =>
      if (assoc cl.owner s.acquiring).isSome || s.isDown c || s.busyExcept cl.owner (some c)
          || (s.inReg c != d.cdFirst) then none
      else some { s with down := c :: s.down, epoch := s.epoch + 1 }
    | none => none
  | .read => some s
  | .look => some s

/-- Where the walker is in `cycleChain`.

* `at c chain`: about to read `c.done.getCount` (and push `c`).
* `owner c chain`: `c` pushed, about to read `c.owner.waitingOn`.
* `check todo chain`: `c.owner eq me` was found; about to read the next claim of `todo` for the final
  `chain.forall(_.done.getCount != 0)`, in the order the list is built (the walker's own claim first,
  the claim it waits on last).
* `done r`: returned `r` (`null` is `none`). -/
inductive WalkSt
  | at (c : ClaimId) (chain : List ClaimId)
  | owner (c : ClaimId) (chain : List ClaimId)
  | check (todo : List ClaimId) (chain : List ClaimId)
  | done (r : Option (List ClaimId))
  deriving DecidableEq, Repr

/-- The walker: who it is, which key it is inside `acquire` of, where its walk stands, the epoch at
the walk's first read, and the result of each finished look with the step index at which it finished. -/
structure Walker where
  me : Who
  k0 : Key
  st : WalkSt
  epoch0 : Nat
  found : Option Nat
  looks : List (Option (List ClaimId) × Nat)
  deriving DecidableEq, Repr

/-- The walker's result so far: `null` while the walk is unfinished. -/
def WalkSt.result : WalkSt → Option (List ClaimId)
  | .done r => r
  | _ => none

/-- The last step of a walk that found a chain: the snapshot check, if the design has one. -/
def finish (d : Design) (s : St) (w : Walker) (chain : List ClaimId) : WalkSt :=
  if d.snapshot && s.epoch != w.epoch0 then .done none else .done (some chain)

/-- A fresh look: `claims.get(key)`; a claim of another claimant starts a walk at it, a free key or a
claim of the walker's own ends the wait without a chain. -/
def look (s : St) (w : Walker) (i : Nat) : Walker :=
  let w := { w with looks := w.looks ++ [(w.st.result, w.found.getD i)], found := none }
  match assoc w.k0 s.reg with
  | some c => if s.owner c == some w.me then { w with st := .done none }
      else { w with st := .at c [], epoch0 := s.epoch }
  | none => { w with st := .done none }

/-- One check of the final loop on claim `c`, `next` being the claim pushed before it (whose owner
was read waiting on `c`): the latch or the registry, and the edge again if the design re-reads it. -/
def finalOk (d : Design) (s : St) (c : ClaimId) (next : Option ClaimId) : Bool :=
  (if d.mapCheck then s.inReg c else !s.isDown c) &&
  (if d.edgeCheck then
    match next with
    | some c' => match s.owner c' with
      | some o => assoc o s.waitingOn == some c
      | none => false
    | none => true
   else true)

/-- One read of `cycleChain`, in the order the Scala code makes them. -/
def readStep (d : Design) (s : St) (w : Walker) : WalkSt :=
  match w.st with
  | .at c chain =>
    if d.i87 && s.isDown c then .done none
    else
      let chain' := c :: chain
      match s.owner c with
      | none => .done none
      | some o =>
        if o == w.me then
          if d.i98 then .check chain' chain' else finish d s w chain'
        else .owner c chain'
  | .owner c chain =>
    match s.owner c with
    | none => .done none
    | some o =>
      match assoc o s.waitingOn with
      | none => .done none
      | some c' => if chain.contains c' then .done none else .at c' chain
  | .check (c :: rest) chain =>
    if finalOk d s c rest.head? then
      match rest with
      | [] => finish d s w chain
      | _ => .check rest chain
    else .done none
  | .check [] chain => finish d s w chain
  | .done r => .done r

/-- A run: the states after each step (the first is the start), and the walker. -/
structure Run where
  states : List St
  walker : Walker
  deriving Repr

/-- Run a history from a state and a walker. `none` if some event is not enabled. -/
def run (d : Design) (s : St) (w : Walker) (evs : List Ev) : Option Run :=
  go evs s w [s] 0
where
  go : List Ev → St → Walker → List St → Nat → Option Run
    | [], _, w, acc, i =>
      some { states := acc.reverse, walker := { w with looks := w.looks ++ [(w.st.result, w.found.getD i)] } }
    | .read :: evs, s, w, acc, i =>
      let st' := readStep d s w
      let found := match w.st, st' with
        | .done _, _ => w.found
        | _, .done (some _) => some i
        | _, _ => w.found
      go evs s { w with st := st', found } (s :: acc) (i + 1)
    | .look :: evs, s, w, acc, i => go evs s (look s w i) (s :: acc) (i + 1)
    | ev :: evs, s, w, acc, i =>
      match bg d s ev with
      | some s' => go evs s' w (s' :: acc) (i + 1)
      | none => none

/-- The walker at the start: inside `acquire k0`, its first look taken on the start state. -/
def walker0 (s : St) (me : Who) (k0 : Key) : Walker :=
  let w : Walker := { me, k0, st := .done none, epoch0 := 0, found := none, looks := [] }
  { look s w 0 with looks := [] }

/-! ## 2. Ground truth -/

/-- Follow "is inside `acquire(k)`" and "`k`'s registered claim is owned by" from `w`, `n` steps at
most: does it come back to `me`? -/
def follow (s : St) (me : Who) : Nat → Who → Bool
  | 0, _ => false
  | n + 1, w =>
    match assoc w s.acquiring with
    | none => false
    | some k =>
      match assoc k s.reg with
      | none => false
      | some c =>
        match s.owner c with
        | none => false
        | some o => if o == me then true else follow s me n o

/-- **A real wait-for cycle at one instant**: the walker is inside `acquire` of a key whose registered
claim is held by a claimant inside `acquire` of a key whose registered claim is held by ... the
walker. Nothing about `waitingOn` or the latches: this is the deadlock, which the walk approximates. -/
def realCycle (s : St) (me : Who) : Bool := follow s me (s.claims.length + 1) me

/-- The chain the walker's last look returned, if any. -/
def Run.chain (r : Run) : Option (List ClaimId) := r.walker.st.result

/-- Was there a real cycle at some instant up to and including step `i`? -/
def Run.realBy (r : Run) (i : Nat) : Bool :=
  (r.states.take (i + 1)).any fun s => realCycle s r.walker.me

/-- Did the last look return a chain? -/
def Run.found (r : Run) : Bool := r.chain.isSome

/-- Was there a real cycle at some instant before the chain was returned? -/
def Run.everReal (r : Run) : Bool :=
  match r.walker.looks.reverse with
  | (some _, j) :: _ => r.realBy j
  | _ => false

/-- Was there a real cycle at the instant the chain was returned? -/
def Run.realAtFound (r : Run) : Bool :=
  match r.walker.looks.reverse with
  | (some _, j) :: _ => match r.states[j]? with
    | some s => realCycle s r.walker.me
    | none => false
  | _ => false

/-- **A false chain**: the walk returned a chain and no instant up to then had a real cycle. -/
def Run.falseChain (r : Run) : Bool := r.found && !r.everReal

/-- A chain real at some instant but not at the instant it was returned: a cycle another party has
begun to resolve. -/
def Run.transient (r : Run) : Bool := r.found && r.everReal && !r.realAtFound

/-- Did two consecutive looks return the same chain (the two-looks rule's test, `corresponds(_ eq _)`)? -/
def Run.twoLooksSame (r : Run) : Bool :=
  match r.walker.looks.reverse with
  | (some c, _) :: (some c', _) :: _ => c == c'
  | _ => false

/-- Does the history contain an `unwind`? -/
def hasUnwind (evs : List Ev) : Bool := evs.any fun | .unwind _ => true | _ => false

/-- The analysis of one history over a design: `none` if the history is not enabled. -/
def analyse (d : Design) (n : Nat) (me : Who) (k0 : Key) (evs : List Ev) : Option Run :=
  let s := St.init n me k0
  run d s (walker0 s me k0) evs

/-! ## 3. The two findings reconstructed

Three claimants: `W = 0` holds key `0` (claim `0`) and is inside `acquire 1`; `A = 1` holds key `1`
(claim `1`); `B = 2` holds key `2` (claim `2`). -/

/-- The walker. -/
def W : Who := 0
/-- The first other claimant. -/
def A : Who := 1
/-- The second other claimant. -/
def B : Who := 2

/-- Three claimants, the walker inside `acquire 1`. -/
def analyse3 (d : Design) (evs : List Ev) : Option Run := analyse d 3 W 1 evs

/-- **I87's history.** `A` waits on `B`'s claim; the walker reads `A`'s claim up and `A.waitingOn`
naming `B`'s claim; `B` releases it (`A` is woken, `waitingOn` not yet cleared) and goes on to wait on
the walker's claim; the walker reads `B`'s released claim and `B.waitingOn`, and meets its own claim.
`A`'s wait ended before `B`'s began. -/
def histI87 : List Ev :=
  [.start A 2, .wait A, .read, .read,
   .remove 2, .countDown 2, .start B 0, .wait B,
   .read, .read, .read]

/-- **I87 reconstructed**: as first written, `cycleChain` returns a chain on `histI87`, and no instant
of the history has a real cycle. -/
theorem i87_false_chain :
    (analyse3 .orig histI87).map Run.falseChain = some true := by decide +kernel

/-- The I87 check alone stops at the released claim: no chain on `histI87`. -/
theorem i87_fix_on_i87 :
    (analyse3 .i87only histI87).map Run.found = some false := by decide +kernel

/-- **I98's history.** The walker reads `A`'s claim up; `A` releases it and then waits on the walker's
claim; the walker reads `A.waitingOn` and meets its own claim. Two waits that never coexisted. -/
def histI98 : List Ev :=
  [.read, .remove 1, .countDown 1, .start A 0, .wait A, .read, .read]

/-- **I98 reconstructed**: with the entry check but not the final one, a chain on `histI98`, and no
instant has a real cycle. -/
theorem i98_false_chain :
    (analyse3 .i87only histI98).map Run.falseChain = some true := by decide +kernel

/-- The final all-held check stops it: no chain on `histI98` with both checks. -/
theorem i98_fix_on_i98 :
    (analyse3 .both histI98).map Run.found = some false := by decide +kernel

/-! ### Spaces

A space is every interleaving of a few claimant programs with the walker's reads, filtered to the
histories the model admits. The theorems over a space are `decide` over all of it. -/

/-- Every merge of two lists keeping each one's order; the fuel is structural so that `decide` can
run it. -/
def merge : Nat → List Ev → List Ev → List (List Ev)
  | 0, _, _ => []
  | _ + 1, [], r => [r]
  | _ + 1, l, [] => [l]
  | n + 1, a :: l, b :: r => (merge n l (b :: r)).map (a :: ·) ++ (merge n (a :: l) r).map (b :: ·)

/-- Every interleaving of the lists. -/
def interleave : List (List Ev) → List (List Ev)
  | [] => [[]]
  | [p] => [p]
  | p :: ps => (interleave ps).flatMap fun r => merge (p.length + r.length + 1) p r

/-- `n` reads of the walker. -/
def reads (n : Nat) : List Ev := List.replicate n .read

/-- The histories of a space the model admits under a design. -/
def admitted (d : Design) (an : Design → List Ev → Option Run) (space : List (List Ev)) :
    List (List Ev) :=
  space.filter fun evs => (an d evs).isSome

/-- Every admitted history of a space satisfies `p` of its run under design `d`. -/
def allRuns (d : Design) (an : Design → List Ev → Option Run) (space : List (List Ev))
    (p : List Ev → Run → Bool) : Bool :=
  space.all fun evs =>
    match an d evs with
    | some r => p evs r
    | none => true

/-- **Space I98**: `A` releases its claim and then waits on the walker's, under a two-claim walk of
up to five reads placed anywhere. -/
def spaceI98 : List (List Ev) :=
  interleave [[.remove 1, .countDown 1, .start A 0, .wait A], reads 5]

/-- **The final check subsumes the entry check.** On space I98 (and on the release-window space
below) the walk with the final check alone returns a chain exactly when the walk with both does: a
claim counted down before it was pushed is still down at the end, since a latch counts down once.
The entry check only ends the walk sooner. -/
theorem entry_check_subsumed :
    allRuns .i98only analyse3 spaceI98
      (fun evs r => r.found == ((analyse3 .both evs).map Run.found == some true)) = true := by
  decide +kernel

/-- Without the I98 check, space I98 has false chains; with it, none. -/
theorem spaceI98_i87only_false :
    (admitted .i87only analyse3 spaceI98).any
      (fun evs => (analyse3 .i87only evs).map Run.falseChain == some true) = true := by decide +kernel

theorem spaceI98_both_sound :
    allRuns .both analyse3 spaceI98 (fun _ r => !r.falseChain) = true := by decide +kernel

/-! ## 4. What remains with both checks: the release window and the unwinding party -/

/-- **The release-window history.** `A` holds claim `1`, waits on `B`'s claim `2`. The walker reads
claim `1` up and `A.waitingOn` naming claim `2`. `A`'s `await` returns and `A` throws out of
`acquire` (an abort as another cycle's victim, a `cycle()` raise, an interrupt): `waitingOn` is
cleared in the `finally`, and `A` begins to release claim `1`: `claims.remove` runs, `countDown` not
yet. `B` now enters `acquire 0` and waits on the walker's claim. The walker reads claim `2` up,
`B.waitingOn` naming claim `0`, claim `0` up and its own; the final check finds claims `0`, `2` and
`1` all up, claim `1` because its latch is still up in the window. `A`'s wait ended before `B`'s
began: no instant has a cycle. -/
def histWindow : List Ev :=
  [.start A 2, .wait A, .read, .read,
   .wake A, .unwind A, .remove 1,
   .start B 0, .wait B,
   .read, .read, .read, .read, .read, .read,
   .countDown 1]

/-- **A false chain with both checks**: `cycleChain` as at retronym/scala3#84 returns a chain on
`histWindow`, and no instant has a real cycle. The I98 argument ("a claim still held now was held
throughout the walk, and the waits on them still stand") fails in its second half: a latch that is
up says the owner has not counted down, not that the owner still waits, and `A`'s wait has ended. -/
theorem release_window_false_chain :
    (analyse3 .both histWindow).map Run.falseChain = some true := by decide +kernel

/-- Counting down before removing closes `histWindow`: the walker's final check finds claim `1`
down. -/
def histWindowCd : List Ev :=
  [.start A 2, .wait A, .read, .read,
   .wake A, .unwind A, .countDown 1,
   .start B 0, .wait B,
   .read, .read, .read, .read, .read, .read,
   .remove 1]

theorem cd_first_closes_window :
    (analyse3 .withCdFirst histWindowCd).map Run.found = some false := by decide +kernel

/-- Asking the registry closes `histWindow` too: claim `1` is no longer registered. -/
theorem map_check_closes_window :
    (analyse3 .withMapCheck histWindow).map Run.found = some false := by decide +kernel

/-- **The window before the release.** `histWindow` without `A`'s release: `A` has thrown out of its
wait and is unwinding, its claim `1` still registered and up (the `finally` that releases it has not
run yet: between the throw inside the inner `acquire` and the `locked` frame that holds claim `1` are
the frames of the completion, with their own `finally` blocks). The latch and the registry both still
say "held". -/
def histUnwinding : List Ev :=
  [.start A 2, .wait A, .read, .read,
   .wake A, .unwind A,
   .start B 0, .wait B,
   .read, .read, .read, .read, .read, .read]

/-- **Count-down-first and the registry check are not enough**: both return a false chain on
`histUnwinding`. The gap is not between `remove` and `countDown`; it is between a party leaving its
wait and releasing. -/
theorem cd_first_not_enough :
    (analyse3 .withCdFirst histUnwinding).map Run.falseChain = some true ∧
    (analyse3 .withMapCheck histUnwinding).map Run.falseChain = some true := by decide +kernel

/-- Re-reading the edges at the end catches it: `A.waitingOn` no longer names claim `2`. -/
theorem edge_check_closes_unwinding :
    (analyse3 .withEdgeCheck histUnwinding).map Run.found = some false := by decide +kernel

/-- A snapshot catches it: the epoch moved during the walk. -/
theorem snapshot_closes_unwinding :
    (analyse3 .withSnapshot histUnwinding).map Run.found = some false := by decide +kernel

/-- The background of `histWindow` in one order: `A` waits, is woken, unwinds, removes; `B` waits on
the walker; `A` counts down. -/
def bgWindow : List Ev :=
  [.start A 2, .wait A, .wake A, .unwind A, .remove 1, .start B 0, .wait B, .countDown 1]

/-- **Space W**: `bgWindow` with the walker's eight reads placed anywhere among its steps (12870
histories, every placement). -/
def spaceW : List (List Ev) := interleave [bgWindow, reads 8]

/-- **Space W without the unwind**: `A` waits, is woken, and waits again; `B` waits on the walker.
Every wait here stands. -/
def spaceNoUnwind : List (List Ev) :=
  interleave [[.start A 2, .wait A, .wake A, .wait A, .start B 0, .wait B], reads 8]

/-- **Space R**: `B` releases its claim normally (no unwind) while `A` waits on it; `A`, woken, takes
key `2` over with a new claim; `B` goes on to wait on the walker. A release window, a woken waiter
with a stale `waitingOn`, a key taken over, nobody throwing (12870 histories). -/
def spaceRelease : List (List Ev) :=
  interleave [[.start A 2, .wait A, .remove 2, .countDown 2, .wake A, .grant A,
               .start B 0, .wait B], reads 8]

/-- Space W is not empty of false chains under both checks. -/
theorem spaceW_has_false_chain :
    (admitted .both analyse3 spaceW).any
      (fun evs => (analyse3 .both evs).map Run.falseChain == some true) = true := by decide +kernel

/-- **Without an unwind, both checks are sound**: every chain returned on `spaceNoUnwind` has a real
cycle at some instant up to its return. -/
theorem no_unwind_sound :
    allRuns .both analyse3 spaceNoUnwind (fun _ r => !r.falseChain) = true := by decide +kernel

/-- The same on space R: a release window, a stale `waitingOn` of a woken waiter and a key taken over
by a new claim during the walk never make a false chain. -/
theorem release_sound :
    allRuns .both analyse3 spaceRelease (fun _ r => !r.falseChain) = true := by decide +kernel

/-- **Every false chain under both checks has an unwind in its history**: the two theorems above are
this statement on the spaces without one, and on space W, where every history has one, it says
nothing more; the three together, as one statement over the union, are the `native_decide` example
below. -/
theorem false_chain_needs_unwind :
    allRuns .both analyse3 (spaceNoUnwind ++ spaceRelease)
      (fun evs r => !r.falseChain || hasUnwind evs) = true := by decide +kernel

/-- `bgWindow` with the release in the count-down-first order, and `B`'s wait before `A` begins to
release, so that the window between `A`'s throw and its release is open while `B` waits. -/
def bgWindowCd : List Ev :=
  [.start A 2, .wait A, .wake A, .unwind A, .start B 0, .wait B, .countDown 1, .remove 1]

/-- Space W in the count-down-first order. -/
def spaceWCd : List (List Ev) := interleave [bgWindowCd, reads 8]

/-- **Count-down-first still has false chains** on its space: the window before the release. -/
theorem spaceWCd_has_false_chain :
    (admitted .withCdFirst analyse3 spaceWCd).any
      (fun evs => (analyse3 .withCdFirst evs).map Run.falseChain == some true) = true := by decide +kernel

/-- **The edge re-check is sound on the spaces**: with count-down-first and the edges re-read, every
chain returned has a real cycle at some instant. -/
theorem edge_check_sound :
    allRuns .withEdgeCheck analyse3 (spaceWCd ++ spaceNoUnwind) (fun _ r => !r.falseChain) = true := by
  decide +kernel

/-- **The snapshot is sound on the spaces**: with a sequence number compared before and after, every
chain returned has a real cycle at the instant it is returned. -/
theorem snapshot_sound :
    allRuns .withSnapshot analyse3 (spaceW ++ spaceNoUnwind) (fun _ r => !r.found || r.realAtFound) = true := by
  decide +kernel

/-- The full interleavings of the programs of space W (`A`'s six steps, `B`'s two, the eight reads:
180180 histories), by the compiled evaluator: the same three statements. -/
example :
    let space := interleave [[.start A 2, .wait A, .wake A, .unwind A, .remove 1, .countDown 1],
                             [.start B 0, .wait B], reads 8]
    allRuns .both analyse3 space (fun evs r => !r.falseChain || hasUnwind evs) = true ∧
    allRuns .withSnapshot analyse3 space (fun _ r => !r.found || r.realAtFound) = true ∧
    (admitted .both analyse3 space).any
      (fun evs => (analyse3 .both evs).map Run.falseChain == some true) = true := by
  native_decide

/-- The full interleavings of the count-down-first programs (180180), the edge re-check sound on all. -/
example :
    let space := interleave [[.start A 2, .wait A, .wake A, .unwind A, .countDown 1, .remove 1],
                             [.start B 0, .wait B], reads 8]
    allRuns .withEdgeCheck analyse3 space (fun _ r => !r.falseChain) = true := by
  native_decide

/-! ## 5. Two looks, and the first look -/

/-- **Two looks at the window.** After `histWindow`'s chain the walker's `await` times out and it
looks again: `A` is unwinding, so `A.waitingOn` is null and the second look finds no chain. The
two-looks rule does not raise on this false chain. -/
def histTwoLooks : List Ev := histWindow ++ [.look, .read, .read]

theorem two_looks_window_not_repeated :
    (analyse3 .both histTwoLooks).map Run.twoLooksSame = some false := by decide +kernel

/-- **A repeated chain that is real.** `A` waits on `B`, `B` on the walker; two looks, the same chain,
and a real cycle at both. -/
def histTwoLooksReal : List Ev :=
  [.start A 2, .wait A, .start B 0, .wait B,
   .read, .read, .read, .read, .read, .read, .read, .read,
   .look, .read, .read, .read, .read, .read, .read, .read, .read]

theorem two_looks_real_example :
    (analyse3 .both histTwoLooksReal).map (fun r => r.twoLooksSame && r.realAtFound) = some true := by
  decide +kernel

/-- **Space L**: after `histUnwinding`'s false chain (`A` unwinding, its claim still registered) the
walker looks again; its eight reads are placed anywhere among `A`'s release and `B`'s next slice
(715 histories). -/
def spaceTwoLooks : List (List Ev) :=
  (interleave [[.remove 1, .countDown 1, .wake B, .wait B], .look :: reads 8]).map (histUnwinding ++ ·)

/-- **Space L2**: two looks over `bgWindow`, the first look's reads and the second's placed anywhere,
by the compiled evaluator below; here the first look is fixed to `histWindow`'s placement. -/
def spaceTwoLooksFull : List (List Ev) := interleave [bgWindow, reads 8 ++ [.look] ++ reads 8]

/-- **Two consecutive looks with the same chain imply a cycle real at some instant**, on space L with
both checks: `histUnwinding`'s false chain is never repeated, whatever the second look sees. The
argument the space confirms: the second look re-reads every edge, so every party of the chain is
inside `acquire` during the second look and none unwound during the first (a party that unwinds
never waits again, and its claim is the same object in both chains), so the first look read waits
that all stood at its end. The two-looks rule is sound here. -/
theorem two_looks_real :
    allRuns .both analyse3 spaceTwoLooks (fun _ r => !r.twoLooksSame || r.everReal) = true := by
  decide +kernel

/-- The same over every placement of both looks' reads among `bgWindow` (1081575 histories), by the
compiled evaluator. -/
example :
    allRuns .both analyse3 spaceTwoLooksFull (fun _ r => !r.twoLooksSame || r.everReal) = true := by
  native_decide

/-- **The first look.** A claimant that `canAbort` aborts on the chain of its first look. On
`histWindow` with both checks that chain is false: a body-typing reader is cancelled and restarted
for a cycle that never was. The abort is cheap (the request is retried) and needs a party that left
its wait by unwinding during the walk, so it is bounded by the rate of unwinds; `edgeCheck` or
`snapshot` remove it. -/
theorem first_look_false_abort :
    (analyse3 .both histWindow).map Run.falseChain = some true ∧
    (analyse3 .withEdgeCheck histUnwinding).map Run.found = some false := by decide +kernel

/-! ## 6. What the model leaves out

* One claimant per thread. A claimant that moves between threads, or two threads under one claimant,
  break the "`waitingOn` non-null means inside `acquire`" reading the arguments use.
* Re-entrance (`holds > 1`): the owner never waits on its own claim, so it adds nothing to the graph.
* The claimant's own decision on a chain (abort, wait for an abortable party, the two-looks rule) is
  not an event; `unwind` stands for any way out of `acquire` that throws. The note says which of those
  the real system has.
* The 1000-step bound of `cycleChain`: a walk that revisits a claim without reaching the walker ends
  with `null`, as the bound does.
* Time: a slice is 5 ms, a release window is two statements. The model has orders only, so a
  history that needs a window longer than a slice is admitted; the note weighs it. -/

end Query.WaitGraph
