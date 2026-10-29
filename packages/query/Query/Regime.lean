import Query.Basic
/-!
# The read/write regime

`InteractiveDriver` serves requests as readers and changes the source of truth as a writer (the
design's §2 and §10.3): a writer raises a sticky cancel flag, admits no new reader, waits until every
running reader reaches its next checkpoint and unwinds, then mutates and clears the flag; a reader
the writer cancelled is retried by its caller on the new content. This is IntelliJ's pending write
action cancelling read actions at their next `checkCanceled`, and K2's modification events. The
model has content versions, readers that read the version at each step, and checkpoints at a
distance that varies per reader (a long implicit search has none for many steps, I11).

* **The machine** (§1). A reader is waiting, running (the steps left, the steps to its next
  checkpoint, the versions read so far) or done; the state is the version, the flag and the readers.
  Actions: admit a reader, step a reader, a writer arrives, a writer writes (only once no reader of
  the regime runs). The one parameter is writer preference: whether a pending writer blocks
  admission. A `rogue` reader is one admitted outside the regime (I50).
* **One version per request** (§2). `run_inv`, by induction over every schedule: every reader's
  reads are of the version current while it ran, so a finished request has read one version
  (`done_one_version`). This is what "snapshots are not needed" rests on: a reader never crosses a
  write, because the write waits for it to unwind.
* **Write latency** (§3). `reader_leaves_within`: with the flag up, a running reader is gone after
  as many of its steps as the lesser of its remaining work and its distance to its next checkpoint.
  The writer's wait is the longest such distance among the running readers (`latency_is_longest_gap`
  on two readers, gaps 2 and 7), plus the write; the reader with no checkpoint (I11) is the bound.
* **Writer starvation** (§4). Without preference a stream of requests keeps a reader running at
  every moment and the writer never gets in (`writer_starves_forever`, a period that maps the state to
  itself). With preference admission is refused while a writer is pending (`admit_pref_pending`, for
  every state), so the running readers drain and the write lands within the same period
  (`pref_writer_lands`).
* **Reader starvation** (§5). Edits faster than a request's work cancel it at every checkpoint and
  the request is never answered (`reader_starves_forever`, by a state family indexed by the version):
  IntelliJ's `nonBlocking` read action's problem. What mitigates it is fewer writers: the body-edit
  rule keeps the run across an edit inside a body, so a keystroke stream is mostly not a write stream
  (another model); and a bounded number of retries before a reader is let through as a writer
  (IntelliJ's `executeSynchronously`).
* **I50** (§6). Two executors over one driver: a reader admitted outside the regime is not waited
  for, and reads two versions in one request (`rogue_reads_two_versions`), the stock Metals
  "denotation invalid in run" after a queue reset; the same reader inside the regime holds the write
  back (`regime_reader_holds_write`).
-/

namespace Query.Regime

/-! ## 1. The machine -/

/-- A reader's state: not admitted (or cancelled, awaiting its caller's retry); running with
`left` steps of work, `toCp` steps to its next checkpoint, and the versions it has read; or done. -/
inductive RState
  | waiting
  | running (left toCp : Nat) (reads : List Nat)
  | done (reads : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A request slot: its work in steps, its checkpoint gap (`len` or more for a request with no
checkpoint, I11), whether it is admitted outside the regime (I50), and its state. -/
structure Reader where
  len : Nat
  gap : Nat
  rogue : Bool
  state : RState
  deriving DecidableEq, Repr, Inhabited

/-- The driver: the content version, the sticky cancel flag (a writer is pending), the readers. -/
structure St where
  ver : Nat
  pending : Bool
  readers : List Reader
  deriving DecidableEq, Repr

def Reader.running (r : Reader) : Bool :=
  match r.state with
  | .running .. => true
  | _ => false

def Reader.isDone (r : Reader) : Bool :=
  match r.state with
  | .done _ => true
  | _ => false

def Reader.reads (r : Reader) : List Nat :=
  match r.state with
  | .running _ _ rs => rs
  | .done rs => rs
  | .waiting => []

/-- All reads are of one version. -/
def oneVersion (reads : List Nat) : Bool :=
  match reads with
  | [] => true
  | v :: rest => rest.all (· == v)

/-- One step of a reader: it reads the current version; at the end of its work it is done; at a
checkpoint it unwinds if a writer is pending (a rogue reader polls no flag); else it goes on. -/
def stepR (ver : Nat) (pending : Bool) (r : Reader) : Reader :=
  match r.state with
  | .running left toCp reads =>
    let reads := reads ++ [ver]
    if left - 1 = 0 then { r with state := .done reads }
    else if toCp - 1 = 0 then
      if pending && !r.rogue then { r with state := .waiting }
      else { r with state := .running (left - 1) r.gap reads }
    else { r with state := .running (left - 1) (toCp - 1) reads }
  | _ => r

/-- Admit a reader that is not running (a new request on the slot): refused while a writer is
pending if the regime prefers writers; a rogue reader is admitted regardless. -/
def admitR (pref pending : Bool) (r : Reader) : Reader :=
  match r.state with
  | .running .. => r
  | _ => if pref && pending && !r.rogue then r else { r with state := .running r.len r.gap [] }

def modifyAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, a :: l => f a :: l
  | n + 1, a :: l => a :: modifyAt f n l

/-- A reader of the regime is running: the writer must wait. -/
def St.busy (st : St) : Bool := st.readers.any fun r => r.running && !r.rogue

inductive Act | admit (i : Nat) | step (i : Nat) | arrive | write
  deriving DecidableEq, Repr

/-- One action under a regime with (`pref`) or without writer preference. -/
def act (pref : Bool) (st : St) : Act → St
  | .admit i => { st with readers := modifyAt (admitR pref st.pending) i st.readers }
  | .step i => { st with readers := modifyAt (stepR st.ver st.pending) i st.readers }
  | .arrive => { st with pending := true }
  | .write => if st.pending && !st.busy then { st with ver := st.ver + 1, pending := false } else st

def run (pref : Bool) : List Act → St → St
  | [], st => st
  | x :: xs, st => run pref xs (act pref st x)

theorem run_append (pref : Bool) (a b : List Act) (st : St) :
    run pref (a ++ b) st = run pref b (run pref a st) := by
  induction a generalizing st with
  | nil => rfl
  | cons x xs ih => simp [run, ih]

def periods (p : List Act) : Nat → List Act
  | 0 => []
  | m + 1 => periods p m ++ p

def St.reader (st : St) (i : Nat) : Reader := st.readers.getD i default

/-- A slot before any request: `len` steps of work, a checkpoint every `gap`. -/
def slot (len gap : Nat) (rogue : Bool := false) : Reader := ⟨len, gap, rogue, .waiting⟩

/-! ## 2. One version per request -/

theorem mem_modifyAt {α : Type} (f : α → α) (i : Nat) (l : List α) (x : α)
    (h : x ∈ modifyAt f i l) : x ∈ l ∨ ∃ y ∈ l, x = f y := by
  induction l generalizing i with
  | nil => simp [modifyAt] at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [modifyAt, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr ⟨a, List.mem_cons_self .., rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ i =>
      simp only [modifyAt, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih i h with h | ⟨y, hy, rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

/-- Every read is of version `v`. -/
def OneVersion (v : Nat) (reads : List Nat) : Prop := ∀ x ∈ reads, x = v

/-- The invariant: no reader is rogue, a running reader has read only the current version, a done
reader has read one version. -/
def Inv (st : St) : Prop :=
  ∀ r ∈ st.readers, r.rogue = false ∧
    (∀ left toCp reads, r.state = .running left toCp reads → OneVersion st.ver reads) ∧
    (∀ reads, r.state = .done reads → ∃ v, OneVersion v reads)

theorem busy_false {st : St} (h : st.busy = false) {r : Reader} (hr : r ∈ st.readers)
    (hg : r.rogue = false) : r.running = false := by
  unfold St.busy at h
  rw [List.any_eq_false] at h
  have := h r hr
  cases hrun : r.running <;> simp_all

theorem admitR_inv (pref pending : Bool) (ver : Nat) {r : Reader}
    (h : r.rogue = false ∧
      (∀ left toCp reads, r.state = .running left toCp reads → OneVersion ver reads) ∧
      (∀ reads, r.state = .done reads → ∃ v, OneVersion v reads)) :
    (admitR pref pending r).rogue = false ∧
      (∀ left toCp reads, (admitR pref pending r).state = .running left toCp reads →
        OneVersion ver reads) ∧
      (∀ reads, (admitR pref pending r).state = .done reads → ∃ v, OneVersion v reads) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold admitR
  split
  · exact ⟨h1, h2, h3⟩
  · split
    · exact ⟨h1, h2, h3⟩
    · refine ⟨h1, ?_, ?_⟩
      · intro left toCp reads hs
        simp only at hs
        cases hs
        intro x hx; simp at hx
      · intro reads hs; simp at hs

theorem stepR_inv (pending : Bool) (ver : Nat) {r : Reader}
    (h : r.rogue = false ∧
      (∀ left toCp reads, r.state = .running left toCp reads → OneVersion ver reads) ∧
      (∀ reads, r.state = .done reads → ∃ v, OneVersion v reads)) :
    (stepR ver pending r).rogue = false ∧
      (∀ left toCp reads, (stepR ver pending r).state = .running left toCp reads →
        OneVersion ver reads) ∧
      (∀ reads, (stepR ver pending r).state = .done reads → ∃ v, OneVersion v reads) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold stepR
  split
  · rename_i left toCp reads hs
    have hone : OneVersion ver (reads ++ [ver]) := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 left toCp reads hs x hx
      · rfl
    simp only
    split
    · refine ⟨h1, ?_, ?_⟩
      · intro _ _ _ hs'; simp at hs'
      · intro reads' hs'; simp only at hs'; cases hs'; exact ⟨ver, hone⟩
    · split
      · split
        · refine ⟨h1, ?_, ?_⟩
          · intro _ _ _ hs'; simp at hs'
          · intro _ hs'; simp at hs'
        · refine ⟨h1, ?_, ?_⟩
          · intro _ _ reads' hs'; simp only at hs'; cases hs'; exact hone
          · intro _ hs'; simp at hs'
      · refine ⟨h1, ?_, ?_⟩
        · intro _ _ reads' hs'; simp only at hs'; cases hs'; exact hone
        · intro _ hs'; simp at hs'
  · exact ⟨h1, h2, h3⟩

/-- Every action keeps the invariant. The write's case is the regime: it happens only when no
reader runs, so the version change is seen by nobody mid-request. -/
theorem act_inv (pref : Bool) (st : St) (a : Act) (h : Inv st) : Inv (act pref st a) := by
  cases a with
  | admit i =>
    intro r hr
    simp only [act] at hr
    rcases mem_modifyAt _ _ _ _ hr with hr | ⟨y, hy, rfl⟩
    · exact h r hr
    · exact admitR_inv pref st.pending st.ver (h y hy)
  | step i =>
    intro r hr
    simp only [act] at hr
    rcases mem_modifyAt _ _ _ _ hr with hr | ⟨y, hy, rfl⟩
    · exact h r hr
    · exact stepR_inv st.pending st.ver (h y hy)
  | arrive => exact h
  | write =>
    simp only [act]
    split
    · rename_i hw
      intro r hr
      obtain ⟨h1, h2, h3⟩ := h r hr
      refine ⟨h1, ?_, h3⟩
      intro left toCp reads hs
      have hb : st.busy = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
        exact hw.2
      have := busy_false hb hr h1
      simp [Reader.running, hs] at this
    · exact h

theorem run_inv (pref : Bool) (acts : List Act) (st : St) (h : Inv st) : Inv (run pref acts st) := by
  induction acts generalizing st with
  | nil => exact h
  | cons a acts ih => exact ih _ (act_inv pref st a h)

/-- A fresh driver: no reader admitted, none rogue. -/
def Fresh (st : St) : Prop := ∀ r ∈ st.readers, r.rogue = false ∧ r.state = .waiting

theorem Fresh.inv {st : St} (h : Fresh st) : Inv st := by
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  refine ⟨h1, ?_, ?_⟩
  · intro _ _ _ hs; rw [h2] at hs; cases hs
  · intro _ hs; rw [h2] at hs; cases hs

/-- Under every schedule, from a fresh driver, a finished request has read one version: the
reader never needed a snapshot. -/
theorem done_one_version (pref : Bool) (acts : List Act) (st : St) (h : Fresh st) (r : Reader)
    (hr : r ∈ (run pref acts st).readers) (reads : List Nat) (hd : r.state = .done reads) :
    ∃ v, OneVersion v reads :=
  ((run_inv pref acts st h.inv) r hr).2.2 reads hd

/-! ## 3. Write latency -/

/-- `n` steps of one reader with the flag up. -/
def iterR (ver : Nat) : Nat → Reader → Reader
  | 0, r => r
  | n + 1, r => iterR ver n (stepR ver true r)

theorem stepR_not_running (ver : Nat) (pending : Bool) {r : Reader} (h : r.running = false) :
    (stepR ver pending r).running = false := by
  unfold stepR
  split
  · rename_i hs; simp [Reader.running, hs] at h
  · exact h

theorem iterR_not_running (ver n : Nat) {r : Reader} (h : r.running = false) :
    (iterR ver n r).running = false := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih => exact ih (stepR_not_running ver true h)

/-- A running reader of the regime is gone, finished or unwound, after `min left toCp` of its steps
with the flag up: its remaining work or its distance to the next checkpoint, whichever is less. -/
theorem reader_leaves_within (ver n : Nat) : ∀ (r : Reader) (left toCp : Nat) (reads : List Nat),
    r.state = .running left toCp reads → r.rogue = false → min left toCp ≤ n + 1 →
    (iterR ver (n + 1) r).running = false := by
  induction n with
  | zero =>
    intro r left toCp reads hs hg hle
    simp only [iterR]
    unfold stepR
    rw [hs]
    simp only [hg, Bool.not_false, Bool.and_true]
    split
    · rfl
    · split
      · rfl
      · omega
  | succ n ih =>
    intro r left toCp reads hs hg hle
    show (iterR ver (n + 1) (stepR ver true r)).running = false
    unfold stepR
    rw [hs]
    simp only [hg, Bool.not_false, Bool.and_true]
    split
    · exact iterR_not_running ver (n + 1) rfl
    · split
      · exact iterR_not_running ver (n + 1) rfl
      · exact ih _ (left - 1) (toCp - 1) _ rfl rfl (by omega)

/-- Two readers of ten steps: one polls every two, the other (a long implicit search, I11) only at
its seventh. The writer arrives; the first reader leaves at its second step, the second holds the
write back for six of its steps and leaves at the seventh; the write then lands. The latency is the
longest gap, plus the write. -/
def twoGaps : St := ⟨0, false, [slot 10 2, slot 10 7]⟩

def steps (i n : Nat) : List Act := List.replicate n (.step i)

theorem latency_is_longest_gap :
    ((run true ([.admit 0, .admit 1, .arrive] ++ steps 0 2) twoGaps).reader 0).running = false ∧
    (run true ([.admit 0, .admit 1, .arrive] ++ steps 0 2 ++ steps 1 6) twoGaps).busy = true ∧
    (run true ([.admit 0, .admit 1, .arrive] ++ steps 0 2 ++ steps 1 6 ++ [.write]) twoGaps).ver = 0 ∧
    (run true ([.admit 0, .admit 1, .arrive] ++ steps 0 2 ++ steps 1 7) twoGaps).busy = false ∧
    (run true ([.admit 0, .admit 1, .arrive] ++ steps 0 2 ++ steps 1 7 ++ [.write]) twoGaps).ver = 1 := by
  decide

/-! ## 4. Writer starvation -/

/-- Two slots of two steps each, re-requested as soon as they finish; a writer pending. -/
def stream : St := ⟨0, true, [⟨2, 2, false, .running 2 2 []⟩, ⟨2, 2, false, .done [0, 0]⟩]⟩

/-- The writer tries, the running reader steps, the other slot's next request is admitted, the
first finishes, the writer tries, and so on: some reader runs at every write attempt. -/
def streamPeriod : List Act :=
  [.write, .step 0, .admit 1, .step 0, .write, .step 1, .admit 0, .step 1]

theorem stream_period_fixes : run false streamPeriod stream = stream := by decide

/-- Without writer preference, no number of periods lets the writer in: the version stays 0 and
the flag stays up. -/
theorem writer_starves_forever (m : Nat) : run false (periods streamPeriod m) stream = stream := by
  induction m with
  | zero => rfl
  | succ m ih => rw [periods, run_append, ih, stream_period_fixes]

theorem modifyAt_id {α : Type} (f : α → α) (i : Nat) (l : List α) (h : ∀ y ∈ l, f y = y) :
    modifyAt f i l = l := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
    cases i with
    | zero => simp [modifyAt, h a (List.mem_cons_self ..)]
    | succ i =>
      simp only [modifyAt, List.cons.injEq, true_and]
      exact ih i fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- With writer preference, admission while a writer is pending is a no-op, in every state whose
readers are the regime's. -/
theorem admit_pref_pending (st : St) (i : Nat) (hp : st.pending = true)
    (hg : ∀ r ∈ st.readers, r.rogue = false) : act true st (.admit i) = st := by
  simp only [act]
  have : modifyAt (admitR true st.pending) i st.readers = st.readers := by
    apply modifyAt_id
    intro y hy
    unfold admitR
    split
    · rfl
    · simp [hp, hg y hy]
  rw [this]

/-- So the same stream under preference drains: the write lands within the period. -/
theorem pref_writer_lands : (run true streamPeriod stream).ver = 1 ∧
    (run true streamPeriod stream).pending = false := by decide

/-! ## 5. Reader starvation -/

/-- One request of four steps polling every two, at version `v`, no writer pending. -/
def edited (v : Nat) : St := ⟨v, false, [slot 4 2]⟩

/-- The request is admitted and takes a step; an edit arrives; the request reaches its checkpoint
and unwinds; the edit lands. -/
def editPeriod : List Act := [.admit 0, .step 0, .arrive, .step 0, .write]

/-- Each period advances the version and leaves the request where it started. -/
theorem edit_period_shifts (v : Nat) : run false editPeriod (edited v) = edited (v + 1) := rfl

/-- Edits faster than the request's work: after any number of edits the request is still waiting,
never answered. The same holds with preference (`run true`): preference is for writers. -/
theorem reader_starves_forever (m : Nat) : run false (periods editPeriod m) (edited 0) = edited m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [periods, run_append, ih, edit_period_shifts]

theorem reader_never_done (m : Nat) :
    ((run false (periods editPeriod m) (edited 0)).reader 0).isDone = false := by
  rw [reader_starves_forever]; rfl

/-! ## 6. I50: a second executor over one driver -/

/-- A reader of the regime and a reader admitted beside it (the old executor's backlog after a
queue reset), each of two steps. -/
def twoExecutors (rogue : Bool) : St := ⟨0, false, [slot 2 2, slot 2 2 rogue]⟩

/-- The second reader is admitted and reads; a writer arrives and, not waiting for a reader it does
not know, writes; the reader's next read is of the new version. -/
def i50 : List Act := [.admit 1, .step 1, .arrive, .write, .step 1]

theorem rogue_reads_two_versions :
    ((run true i50 (twoExecutors true)).reader 1).reads = [0, 1] ∧
    oneVersion ((run true i50 (twoExecutors true)).reader 1).reads = false := by decide

/-- The same reader inside the regime holds the write back until it has finished, and reads one
version. -/
theorem regime_reader_holds_write :
    (run true i50 (twoExecutors false)).ver = 0 ∧
    ((run true i50 (twoExecutors false)).reader 1).reads = [0, 0] ∧
    (run true (i50 ++ [.write]) (twoExecutors false)).ver = 1 := by decide

end Query.Regime
