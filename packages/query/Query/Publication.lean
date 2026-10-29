import Query.Basic
/-!
# Publication idioms over a small weak memory

retronym/scala3#84 makes dotc's symbol table readable by several threads, and adopts three
publication idioms in `dotty.tools.sharing`: a `Stamped` holder (a stamp and a value as one immutable
object in one field), a `Published` field (a period stored with release semantics after the fields
it publishes, loaded with acquire before them), and `Once` (a lazy fact stored into the published
field itself). The design's §4.4 names four shapes of race; this file models the memory the idioms
run on and checks each idiom, and each bug it replaces, by `decide` over every execution of two
threads.

* **The machine** (§1). Memory is a function from a few locations to values; a value is a number, a
  null, or a *holder*, an immutable object of a stamp and a value. Each thread's plain stores wait
  in a per-thread buffer and drain to memory one at a time: under `Arch.weak` in any order that
  keeps the stores to one location in order (store-store reordering, as on Apple silicon); under
  `Arch.tso` oldest first (x86). A load reads the thread's own newest buffered store to the location
  if there is one (store-to-load forwarding), else memory; under `weak` it may instead return the
  thread's *view* of the location, what it last saw there (the stale read of a load reordered before
  an older one), and a load never goes back on a location it has read (coherence). A `release` drains
  the thread's buffer in order and stores after it; an `acquire` is a fresh load that refreshes the
  whole view. The holder is the model's one assumption beyond the hardware: constructing
  `Stamped(s, v)` and publishing its reference is one event, JLS §17.5's final-field guarantee, so a
  reader that sees the reference sees both fields as constructed. `finals` lists every maximal
  execution's end state.
* **Litmus** (§1). Message passing fails with plain stores under `weak` and holds under `tso`
  (`mp_plain_weak_torn`, `mp_plain_tso_ok`); with a release store and a plain load it still fails
  under `weak` (`mp_release_plainLoad_weak_torn`: the reader side needs the acquire on ARM); with
  release and acquire it holds (`mp_release_acquire_weak_ok`).
* **The idioms** (§2). (a) A stamp and a value in two plain fields: torn under `weak` in either store
  order; under `tso` the value-first order is safe and the stamp-first order, dotc's in
  `computeDenot` before I36, is torn. (b) `Stamped`: every reader sees a whole pair, two writers
  cannot be mixed, and a field read twice (shape 3, I67) can see two holders. (c) `cachedIf`: a value
  not kept leaves a holder right for its own stamp. (d) `Published`: message passing holds under
  `weak`; a payload read before the acquire (I78) and a payload store after the release (I36) are
  torn, and in every memory model. (e) `Once`: the fact in the published field is safe and a plain
  reference is the broken double-checked lock; a reset of a flag and a value is torn where a reset of
  one field is not.
* **Periods** (§3). A reader at period 1 and a writer at period 2 never pair a stamp with the other
  period's value (`cross_period_never_confused`): the design's "no fences" holds for the pair. It does
  not extend to the inputs of `compute`: a `cachedWhen` cache invalidated by a store of `Empty`
  loses the invalidation to a racing refill, in every memory model (`clear_loses_invalidation`), while
  an invalidation that bumps a stamp the reader took before its inputs is kept
  (`bump_keeps_invalidation`).
-/

namespace Query.Publication

/-! ## 1. The machine -/

/-- A value in memory: a null (an empty reference, or 0), a number (a period, a flag, a reference
to an object whose fields are modelled as locations), or a holder, the reference to an immutable
`Stamped(stamp, value)`. The holder is one value, never two fields: JLS §17.5, see the module
docstring. -/
inductive Val | null | num (n : Nat) | holder (stamp value : Nat)
  deriving DecidableEq, Repr

/-- `Stamped.Empty`: stamp 0, which is never current, and a null value. -/
def Val.empty : Val := .holder 0 0

/-- A thread's registers. -/
inductive Reg | r0 | r1 | r2
  deriving DecidableEq, Repr

structure Regs where
  r0 : Val
  r1 : Val
  r2 : Val
  deriving DecidableEq, Repr

def Regs.init : Regs := ⟨.null, .null, .null⟩

def Regs.get (rs : Regs) : Reg → Val
  | .r0 => rs.r0
  | .r1 => rs.r1
  | .r2 => rs.r2

def Regs.set (rs : Regs) : Reg → Val → Regs
  | .r0, v => { rs with r0 := v }
  | .r1, v => { rs with r1 := v }
  | .r2, v => { rs with r2 := v }

/-- What a store stores: a constant, a register, or a holder built from a stamp (a constant or a
register) and a register, `new Stamped(n, v)`. A register that is not a number counts as 0. -/
inductive Src
  | val (v : Val)
  | reg (r : Reg)
  | stamped (stamp : Nat) (value : Reg)
  | stampedReg (stamp value : Reg)
  deriving DecidableEq, Repr

def Val.toNat : Val → Nat
  | .num n => n
  | _ => 0

def Src.eval (rs : Regs) : Src → Val
  | .val v => v
  | .reg r => rs.get r
  | .stamped s r => .holder s (rs.get r).toNat
  | .stampedReg s r => .holder (rs.get s).toNat (rs.get r).toNat

/-- An instruction over locations `L`: a plain store, a store conditional on a register (the store
of a `cached` miss, or a double check), a plain load, a release store, an acquire load. -/
inductive Instr (L : Type)
  | store (l : L) (s : Src)
  | storeIf (r : Reg) (test : Val) (l : L) (s : Src)
  | load (l : L) (r : Reg)
  | release (l : L) (s : Src)
  | acquire (l : L) (r : Reg)
  deriving DecidableEq, Repr

/-- How the buffers drain and loads see: `weak`, stores to different locations drain in any order
and a plain load may be stale (ARM, Apple silicon); `tso`, stores drain in order and loads are
fresh (x86). -/
inductive Arch | weak | tso
  deriving DecidableEq, Repr

/-- A thread: its program, its buffer of plain stores not yet in memory (oldest first), its
registers, and its view, the value it last saw at each location (initially the initial memory). -/
structure Thread (L : Type) where
  prog : List (Instr L)
  buf : List (L × Val)
  regs : Regs
  view : L → Val

/-- The state: memory and the two threads, `w` (the writer in most scenarios) and `r`. -/
structure St (L : Type) where
  mem : L → Val
  tw : Thread L
  tr : Thread L

variable {L : Type} [DecidableEq L]

def upd (m : L → Val) (l : L) (v : Val) : L → Val := fun l' => if l' = l then v else m l'

def applyAll (m : L → Val) : List (L × Val) → L → Val
  | [] => m
  | (l, v) :: rest => applyAll (upd m l v) rest

/-- The thread's newest buffered store to `l`, if any: what its own loads of `l` see first. -/
def Thread.forwarded (t : Thread L) (l : L) : Option Val :=
  (t.buf.reverse.find? (·.1 = l)).map (·.2)

/-- The values a plain load of `l` may return: the forwarded store; else memory; and under `weak`
also the thread's view of `l`, when it is older. -/
def Thread.loadValues (arch : Arch) (t : Thread L) (mem : L → Val) (l : L) : List Val :=
  match t.forwarded l with
  | some v => [v]
  | none =>
    match arch with
    | .tso => [mem l]
    | .weak => if t.view l = mem l then [mem l] else [mem l, t.view l]

/-- The thread runs its next instruction: the successor threads (a load has one per value it may
return) with the memory after it (a release writes memory; nothing else does). -/
def Thread.exec (arch : Arch) (mem : L → Val) (t : Thread L) : List (Thread L × (L → Val)) :=
  match t.prog with
  | [] => []
  | .store l s :: rest => [({ t with prog := rest, buf := t.buf ++ [(l, s.eval t.regs)] }, mem)]
  | .storeIf r test l s :: rest =>
    if t.regs.get r = test then [({ t with prog := rest, buf := t.buf ++ [(l, s.eval t.regs)] }, mem)]
    else [({ t with prog := rest }, mem)]
  | .load l r :: rest =>
    (t.loadValues arch mem l).map fun v =>
      ({ t with prog := rest, regs := t.regs.set r v, view := upd t.view l v }, mem)
  | .release l s :: rest =>
    let v := s.eval t.regs
    [({ t with prog := rest, buf := [], view := upd (applyAll t.view t.buf) l v },
      upd (applyAll mem t.buf) l v)]
  | .acquire l r :: rest =>
    let v := match t.forwarded l with | some v => v | none => mem l
    [({ t with prog := rest, regs := t.regs.set r v, view := upd mem l v }, mem)]

/-- The buffered stores that may drain next under `weak`, each with the buffer without it: any
store with no older store to the same location. -/
def pickAny : List (L × Val) → List ((L × Val) × List (L × Val))
  | [] => []
  | e :: rest =>
    (e, rest) :: (pickAny rest).filterMap fun (e', rest') =>
      if e'.1 = e.1 then none else some (e', e :: rest')

def drains (arch : Arch) (buf : List (L × Val)) : List ((L × Val) × List (L × Val)) :=
  match arch with
  | .weak => pickAny buf
  | .tso => match buf with
    | [] => []
    | e :: rest => [(e, rest)]

/-- Every state one step on: either thread runs an instruction, or one of either thread's buffered
stores reaches memory. A thread's own store, once drained, is in its view: its later loads never
read older than what it stored. -/
def nexts (arch : Arch) (st : St L) : List (St L) :=
  (st.tw.exec arch st.mem).map (fun (t, m) => { st with tw := t, mem := m }) ++
  (st.tr.exec arch st.mem).map (fun (t, m) => { st with tr := t, mem := m }) ++
  (drains arch st.tw.buf).map (fun ((l, v), b) =>
    { st with mem := upd st.mem l v, tw := { st.tw with buf := b, view := upd st.tw.view l v } }) ++
  (drains arch st.tr.buf).map (fun ((l, v), b) =>
    { st with mem := upd st.mem l v, tr := { st.tr with buf := b, view := upd st.tr.view l v } })

/-- Both programs run and both buffers drained. -/
def St.done (st : St L) : Bool :=
  st.tw.prog.isEmpty && st.tw.buf.isEmpty && st.tr.prog.isEmpty && st.tr.buf.isEmpty

/-- The end states of every execution of at most `fuel` steps. Every step runs an instruction or
drains a store, and a store drains once, so `2 * (|pw| + |pr|)` steps end every execution:
`finals` with that fuel is every execution. -/
def finals (arch : Arch) : Nat → St L → List (St L)
  | 0, st => if st.done then [st] else []
  | n + 1, st => if st.done then [st] else (nexts arch st).flatMap (finals arch n)

def init (mem : L → Val) (pw pr : List (Instr L)) : St L :=
  ⟨mem, ⟨pw, [], Regs.init, mem⟩, ⟨pr, [], Regs.init, mem⟩⟩

/-- The end state of every execution of writer `pw` and reader `pr` from memory `mem`. -/
def run (arch : Arch) (mem : L → Val) (pw pr : List (Instr L)) : List (St L) :=
  finals arch (2 * (pw.length + pr.length)) (init mem pw pr)

/-- The reader's registers at the end. -/
def St.rr (st : St L) : Regs := st.tr.regs

/-- A cache hit at stamp `now` on the loaded holder: its value when the stamp is current, else a
miss. -/
def hitAt (now : Nat) : Val → Option Nat
  | .holder s v => if s = now then some v else none
  | _ => none

/-! ### Litmus: message passing

A flag and a datum. The writer stores the datum, then the flag; the reader loads the flag, then
the datum. A reader that sees the flag must see the datum. -/

inductive MP | flag | data
  deriving DecidableEq, Repr

def mpInit : MP → Val
  | .flag => .num 0
  | .data => .null

/-- **Plain stores and loads, weak memory: torn.** The flag drains before the datum. -/
theorem mp_plain_weak_torn :
    ∃ st ∈ run .weak mpInit [.store .data (.val (.num 7)), .store .flag (.val (.num 1))]
      [.load .flag .r0, .load .data .r1],
      st.rr.r0 = .num 1 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **Plain stores and loads, TSO: message passing holds.** In-order drains and fresh loads are
enough: an x86 run of the two-field cache cannot see this race. -/
theorem mp_plain_tso_ok :
    ∀ st ∈ run .tso mpInit [.store .data (.val (.num 7)), .store .flag (.val (.num 1))]
      [.load .flag .r0, .load .data .r1],
      st.rr.r0 = .num 1 → st.rr.r1 = .num 7 := by
  decide +kernel

/-- **A release store with a plain load, weak memory: torn.** The writer's order is kept, and the
reader's loads are not: it reads the flag fresh and the datum stale. The acquire is the reader's half
of the protocol, `Published.acquire`, not a courtesy. -/
theorem mp_release_plainLoad_weak_torn :
    ∃ st ∈ run .weak mpInit [.store .data (.val (.num 7)), .release .flag (.val (.num 1))]
      [.load .flag .r0, .load .data .r1],
      st.rr.r0 = .num 1 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **Release and acquire, weak memory: message passing holds.** -/
theorem mp_release_acquire_weak_ok :
    ∀ st ∈ run .weak mpInit [.store .data (.val (.num 7)), .release .flag (.val (.num 1))]
      [.acquire .flag .r0, .load .data .r1],
      st.rr.r0 = .num 1 → st.rr.r1 = .num 7 := by
  decide +kernel

/-! ## 2. The idioms -/

/-! ### (a) A stamp and a value in two plain fields

`if stamp != now then { value = compute; stamp = now }; value`, the design's §4.4.1 shape 1.
The field holds period 1's value `5`; a writer in period 2 stores `7`; a reader in period 2 that
sees stamp 2 must see 7. The torn read pairs the new stamp with the previous period's value (or a
null, I36's `lastSymbol`, I60's `underlyingNormalizable`). -/

inductive SV | stamp | value
  deriving DecidableEq, Repr

def svInit : SV → Val
  | .stamp => .num 1
  | .value => .num 5

def svReader : List (Instr SV) := [.load .stamp .r0, .load .value .r1]

/-- The value stored before the stamp: the order a careful single-threaded author writes. -/
def valueFirst : List (Instr SV) := [.store .value (.val (.num 7)), .store .stamp (.val (.num 2))]

/-- The stamp stored before the value: `Symbol.computeDenot`'s order before I36. -/
def stampFirst : List (Instr SV) := [.store .stamp (.val (.num 2)), .store .value (.val (.num 7))]

abbrev svTorn (st : St SV) : Prop := st.rr.r0 = .num 2 ∧ st.rr.r1 = .num 5

/-- **Value first, weak memory: torn.** The stamp drains first, or the reader's load of the value
is stale. -/
theorem fields_valueFirst_weak_torn : ∃ st ∈ run .weak svInit valueFirst svReader, svTorn st := by
  decide +kernel

/-- **Value first, TSO: never torn.** The two-field cache in this order is correct on x86 by the
hardware alone, which is why a Lincheck stress run on x86 passes it. -/
theorem fields_valueFirst_tso_ok :
    ∀ st ∈ run .tso svInit valueFirst svReader, st.rr.r0 = .num 2 → st.rr.r1 = .num 7 := by
  decide +kernel

/-- **Stamp first, TSO: torn.** The order dotc had in `computeDenot` is wrong in every memory
model: the reader runs between the two stores. -/
theorem fields_stampFirst_tso_torn : ∃ st ∈ run .tso svInit stampFirst svReader, svTorn st := by
  decide +kernel

theorem fields_stampFirst_weak_torn : ∃ st ∈ run .weak svInit stampFirst svReader, svTorn st := by
  decide +kernel

/-- **Two writers, two fields: one's stamp with the other's value**, even under TSO. The reader is
a writer too, in period 3 (stored 8), the other in period 2 (stored 7): the reader's value drains,
the other's value drains over it, and the reader's own stamp is what it reads back. Different
periods make the mix observable; the design's claim is about writers in one period, whose values
are equally valid for it, so the pairing shows only when they differ. -/
theorem fields_two_writers_mixed_tso :
    ∃ st ∈ run .tso svInit valueFirst
      [.store .value (.val (.num 8)), .store .stamp (.val (.num 3)), .load .stamp .r0, .load .value .r1],
      st.rr.r0 = .num 3 ∧ st.rr.r1 = .num 7 := by
  decide +kernel

/-! ### (b) `Stamped`: one holder in one field

The writer allocates `Stamped(2, 7)` and stores the reference plainly; the reader loads the field
once into a local, compares the stamp and returns the value. -/

inductive H | ref
  deriving DecidableEq, Repr

def hInit : H → Val
  | .ref => .holder 1 5

def storeHolder (s v : Nat) : List (Instr H) := [.store .ref (.val (.holder s v))]

/-- **A reader sees a whole pair**, under weak memory, whatever the drain and however stale the
load: the old holder or the new. -/
theorem stamped_whole :
    ∀ st ∈ run .weak hInit (storeHolder 2 7) [.load .ref .r0],
      st.rr.r0 = .holder 1 5 ∨ st.rr.r0 = .holder 2 7 := by
  decide +kernel

/-- **And so a hit is right**: a reader at period 2 returns 7 or misses, never 5. -/
theorem stamped_hit_right :
    ∀ st ∈ run .weak hInit (storeHolder 2 7) [.load .ref .r0],
      hitAt 2 st.rr.r0 = some 7 ∨ hitAt 2 st.rr.r0 = none := by
  decide +kernel

/-- **Two writers cannot be mixed**: the reader that stored `Stamped(3, 8)` reads back its own
holder or the other's, never a stamp of one with a value of the other
(`fields_two_writers_mixed_tso` is the same scenario on two fields). -/
theorem stamped_two_writers_whole :
    ∀ st ∈ run .weak hInit (storeHolder 2 7) [.store .ref (.val (.holder 3 8)), .load .ref .r0],
      st.rr.r0 = .holder 2 7 ∨ st.rr.r0 = .holder 3 8 := by
  decide +kernel

/-- **Shape 3, a field read twice** (I67: `baseTypeCache`'s period found current, then its map
null). A reader that writes `if field.stamp == now then field.value` reads the field twice; an
invalidation to `Empty` between the reads leaves it a current stamp and a null value. The macros
read the field once into `c`; `peek` too. -/
theorem read_twice_torn :
    ∃ st ∈ run .tso (fun _ : H => .holder 2 7) [.store .ref (.val .empty)] [.load .ref .r0, .load .ref .r1],
      hitAt 2 st.rr.r0 = some 7 ∧ st.rr.r1 = .empty := by
  decide +kernel

/-- **Read once**: the same invalidation against one load leaves a hit or a miss, never a null
value with a current stamp. -/
theorem read_once_ok :
    ∀ st ∈ run .weak (fun _ : H => .holder 2 7) [.store .ref (.val .empty)] [.load .ref .r0],
      hitAt 2 st.rr.r0 = some 7 ∨ hitAt 2 st.rr.r0 = none := by
  decide +kernel

/-! ### (c) `cachedIf(keep)`

A value computed but not kept (provisional, under-defined) is not stored: the field keeps the old
holder, right for its own stamp. The writer here is a period-2 reader whose value is not kept, so it
stores nothing. -/

/-- **The old holder is right for its own stamp**: a reader at period 1 hits 5, a reader at period
2 misses and recomputes. -/
theorem cachedIf_old_holder_right :
    ∀ st ∈ run .weak hInit [] [.load .ref .r0],
      hitAt 1 st.rr.r0 = some 5 ∧ hitAt 2 st.rr.r0 = none := by
  decide +kernel

/-! ### (d) `Published`: a period releases its payloads

`Symbol.checkedPeriod` and `NamedType.checkedPeriod`: the payloads (`lastDenot`, `lastSymbol`)
are stored inside a `publishing(period)` block, which ends with the release store of the period;
a payload is read only `after` an `acquired` period. The types forbid the two programs below that
fail. -/

inductive P | period | payload
  deriving DecidableEq, Repr

def pInit : P → Val
  | .period => .num 1
  | .payload => .null

/-- `publishing(2) { payload := 7 }`. -/
def publishOk : List (Instr P) := [.store .payload (.val (.num 7)), .release .period (.val (.num 2))]

/-- `if period.acquire == now then payload.after(snap)`. -/
def readOk : List (Instr P) := [.acquire .period .r0, .load .payload .r1]

/-- **Message passing holds under weak memory.** -/
theorem published_weak_ok :
    ∀ st ∈ run .weak pInit publishOk readOk, st.rr.r0 = .num 2 → st.rr.r1 = .num 7 := by
  decide +kernel

/-- **I78, a payload read before the acquire**: `NamedType.denot` read the denotation before its
period. Torn even under TSO: the writer runs between the two loads. `Payload.after(snap)` needs the
`Acquired` evidence, so this does not compile. -/
theorem payload_before_acquire_torn :
    ∃ st ∈ run .tso pInit publishOk [.load .payload .r1, .acquire .period .r0],
      st.rr.r0 = .num 2 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **I36, a payload stored after the release**: `computeDenot` stored the period, then the
denotation. Torn even under TSO: the reader acquires between the two. `:=` needs the `Publishing`
evidence of the block the release ends, so this does not compile. -/
theorem payload_after_release_torn :
    ∃ st ∈ run .tso pInit [.release .period (.val (.num 2)), .store .payload (.val (.num 7))] readOk,
      st.rr.r0 = .num 2 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **`Published.plain` of the period, then the payload: torn under weak memory**
(`mp_release_plainLoad_weak_torn` on these names). The protocol's `plain` reads are hints checked
again after an acquire, or used only to choose a path. -/
theorem published_plainLoad_weak_torn :
    ∃ st ∈ run .weak pInit publishOk [.load .period .r0, .load .payload .r1],
      st.rr.r0 = .num 2 ∧ st.rr.r1 = .null := by
  decide +kernel

/-! ### (e) `Once`: the fact in the published field

The fact is an object whose own field `field` is written before the reference is stored. `Once`
stores the reference with release semantics and reads it with acquire: a reader that finds it sees
its fields (JCIP §3.5, safe publication). A plain reference is the broken double-checked lock
(JCIP §16.2.4). A separate `done` flag beside a plain value is message passing again, correct with
release and acquire; where it loses is the reset, two stores where `Once.reset` is one. -/

inductive O | once | field | done | value
  deriving DecidableEq, Repr

def oInit : O → Val
  | .once => .null
  | .field => .null
  | .done => .num 1
  | .value => .num 7

/-- **A plain reference, weak memory: the reader sees the object before its field.** -/
theorem once_plain_weak_torn :
    ∃ st ∈ run .weak oInit [.store .field (.val (.num 7)), .store .once (.val (.num 1))]
      [.load .once .r0, .load .field .r1],
      st.rr.r0 = .num 1 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **`Once`: release the reference, acquire it; the field is seen.** -/
theorem once_release_acquire_ok :
    ∀ st ∈ run .weak oInit [.store .field (.val (.num 7)), .release .once (.val (.num 1))]
      [.acquire .once .r0, .load .field .r1],
      st.rr.r0 = .num 1 → st.rr.r1 = .num 7 := by
  decide +kernel

/-- **A flag and a value, reset in two plain stores: torn under weak memory**, whichever is stored
first (here the flag first, which is the right order on TSO). -/
theorem flag_reset_weak_torn :
    ∃ st ∈ run .weak oInit [.store .done (.val (.num 0)), .store .value (.val .null)]
      [.acquire .done .r0, .load .value .r1],
      st.rr.r0 = .num 1 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **A flag and a value, reset value first, even with a release of the flag: torn in every
model.** The reader runs between the two stores. -/
theorem flag_reset_valueFirst_tso_torn :
    ∃ st ∈ run .tso oInit [.store .value (.val .null), .release .done (.val (.num 0))]
      [.acquire .done .r0, .load .value .r1],
      st.rr.r0 = .num 1 ∧ st.rr.r1 = .null := by
  decide +kernel

/-- **`Once.reset`, one release store of null**: a reader sees the fact or nothing. -/
theorem once_reset_ok :
    ∀ st ∈ run .weak (fun _ : O => .num 1) [.release .once (.val .null)] [.acquire .once .r0],
      st.rr.r0 = .num 1 ∨ st.rr.r0 = .null := by
  decide +kernel

/-! ## 3. A stamp that is a period

§4.4.1: "A stamped value needs no such argument [that all readers of a run are in one period],
and no fences." The field holds `Stamped(1, 5)`, a reader at period 1 and a writer at period 2. -/

/-- **A reader at period 1 and a writer at period 2 are never confused**: the reader hits 5 or
misses, never 7; a reader at period 2 hits 7 or misses, never 5. No fences, no argument about
periods: the pair's integrity is the holder's. -/
theorem cross_period_never_confused :
    ∀ st ∈ run .weak hInit (storeHolder 2 7) [.load .ref .r0],
      (hitAt 1 st.rr.r0 = some 5 ∨ hitAt 1 st.rr.r0 = none) ∧
      (hitAt 2 st.rr.r0 = some 7 ∨ hitAt 2 st.rr.r0 = none) := by
  decide +kernel

/-! ### What the stamp does not cover: the inputs of `compute`

`ClassDenotation.baseTypeCache` is a `cachedWhen` whose invalidation, `invalidateBaseTypeCache`,
stores `Empty`; Namer calls it after it sets a class's info ("we might have looked before and found
nothing"). A refill reads the field, reads its inputs, computes and stores a holder with the current
stamp. Model: location `cache` is the field, `info` the input; the Namer thread (`w`) stores the new
info and clears the cache; the reader at period 2 refills from the info it read. -/

inductive CI | cache | info | epoch
  deriving DecidableEq, Repr

def ciInit : CI → Val
  | .cache => .empty
  | .info => .num 0
  | .epoch => .num 1

/-- Namer: set the info (released, as the completion's claim does), then clear the cache. -/
def namerClears : List (Instr CI) := [.release .info (.val (.num 1)), .store .cache (.val .empty)]

/-- A refill at period 2: read the field; read the input with acquire; if the field was `Empty`,
store `Stamped(2, info)`. -/
def refill : List (Instr CI) :=
  [.load .cache .r0, .acquire .info .r1, .storeIf .r0 .empty .cache (.stamped 2 .r1)]

/-- **An invalidation by clearing is lost to a racing refill, in every memory model**: the reader
reads `Empty` and the old info, Namer sets the info and clears, the reader stores
`Stamped(2, old info)`. The cache then holds a stale value under a current stamp, and a later
`cachedWhen` test that derives validity from the stamp alone cannot tell. A check-then-act (shape 3)
at the level of the cache: the field was read, then written, and the clear fell between. -/
theorem clear_loses_invalidation :
    ∃ st ∈ run .tso ciInit namerClears refill, st.mem .cache = .holder 2 0 := by
  decide +kernel

/-- Namer: set the info, then bump the epoch with release semantics (the cache's stamp kind). -/
def namerBumps : List (Instr CI) := [.store .info (.val (.num 1)), .release .epoch (.val (.num 2))]

/-- A refill whose stamp is the epoch it acquired before reading its inputs: `Stamped(epoch, info)`. -/
def refillEpoch : List (Instr CI) :=
  [.acquire .epoch .r2, .load .cache .r0, .load .info .r1, .storeIf .r0 .empty .cache (.stampedReg .r2 .r1)]

/-- **An invalidation that bumps the stamp is kept, under weak memory**: a holder stamped with the
new epoch holds the new info; a stale info is stamped with the old epoch, and a reader at the new
epoch misses on it. The stamp was taken before the inputs were read, so the inputs are at least as
new as the stamp. -/
theorem bump_keeps_invalidation :
    ∀ st ∈ run .weak ciInit namerBumps refillEpoch,
      st.mem .cache ∈ [Val.holder 1 0, .holder 1 1, .holder 2 1] := by
  decide +kernel

/-- **The same refill with the stamp taken after the inputs is torn, in every model**: the info is
read before Namer runs and the epoch after. `cached` reads the given `Stamp[K]` first (`val n =
now.value`), then the field, then computes: the right order, and one `compute` must keep by not
caching its inputs in locals read earlier. -/
theorem stamp_after_inputs_torn :
    ∃ st ∈ run .tso ciInit namerBumps
      [.load .cache .r0, .load .info .r1, .acquire .epoch .r2, .storeIf .r0 .empty .cache (.stampedReg .r2 .r1)],
      st.mem .cache = .holder 2 0 := by
  decide +kernel

end Query.Publication
