import ScalaTypes.ToyNamer
/-!
# The scalac kernel of the Java toy, as a state machine over the namer's facts

`packages/scala/probes/interrupt/src/pctoy/Scala2Kernel.java` (with `Global.java`) is scalac's
presentation compiler over the toy language: one thread types the loaded units in the background,
and at each `signalDone` where `interruptsEnabled && lockedCount == 0` services the waiting
requests inside the check in progress. This file is that kernel, line for line where it matters,
with the facts taken from [`ToyNamer.rulesOf`](ToyNamer.lean) instead of its own completers: every
`force` of a member's type is `Query.Lazy.force` on the namer's rules (with a log of the facts it
completed, since each completion is a safepoint), and everything else, the synthetic burst, the
consumed map of synthetic trees, the implicit cache with its generations, the suspended warnings,
the targeted check's `TyperResult`, the scheduler that injects one event at the `k`th safepoint, is
kernel state. `Policy` is the Java `Policy` without the two bits the namer absorbs (`unlockOnUnwind`
and `reuseSymbols`: facts here are keyed by name, scalac's identity reuse).

The harness at the end is `Harness.java`: the background's safepoints are counted, the reference
answers come from the event sent after the background, and for each `k` the event is injected at
safepoint `k` and the answers compared. `results.txt`'s divergent safepoints for the three scalac
kernels are then theorems by `decide`.
-/

namespace ScalaTypes.ToyKernel

open Query Query.Lazy ScalaTypes.ToyNamer

/-- The choices scala/scala#11328 changed, and the proposal. -/
structure Policy where
  uninterruptibleSynthesis : Bool
  keepSyntheticsForTargeted : Bool
  keepFactory : Bool
  suspendTargetedWarnings : Bool
  idempotentSynthetics : Bool
  deriving DecidableEq, Repr

def Policy.before : Policy := ⟨false, false, false, false, false⟩
def Policy.after : Policy := ⟨true, true, true, true, false⟩
def Policy.proposed : Policy := ⟨false, false, true, true, true⟩

inductive Ask
  | completion (file decl member : String)
  | loadedTyped (file : String)
  deriving DecidableEq, Repr

inductive Event
  | request (a : Ask)
  | edit (file : String) (text : Program) (a : Ask)
  deriving DecidableEq, Repr

inductive Answer
  | completion (ty : String) (members : List String)
  | loaded (bodies : List (String × List String)) (problems : List String)
  | text (s : String)
  deriving DecidableEq, Repr

structure Target where
  decl : String
  member : String
  deriving DecidableEq, Repr

/-- A diagnostic: `kind file:decl.member: msg`. Structured, so that the kernel's `decide` never
has to split a string. -/
structure Problem where
  kind : String
  file : String
  decl : String
  member : String
  msg : String
  deriving DecidableEq, Repr

def Problem.render (p : Problem) : String := s!"{p.kind} {p.file}:{p.decl}.{p.member}: {p.msg}"

/-- `TyperResult` and `FreshRunReq`/`CancelException`. -/
inductive Exc
  | typerResult (a : Answer)
  | cancelled

/-- A unit's state (`Global.Unit`): its declarations, the synthetic trees not yet added to a body
(body key, name, the declaration they came from), the reporting state, the typed bodies. -/
structure UnitSt where
  name : String
  decls : Program
  synthetics : List (String × String × Nat) := []
  /-- The namer's synthetic trees, for a check that starts from its own copy. -/
  synthetics0 : List (String × String × Nat) := []
  suspended : List Problem := []
  problems : List Problem := []
  suppressions : List String := []
  suppressionsKnown : Bool := false
  bodies : List (String × List String) := []
  typed : Bool := false
  implicitCache : Option (List (String × Nat)) := none

/-- How requests are served. `nested`: scalac today, inside the check at a safepoint. `abort`: a
request waiting at a safepoint unwinds the background check, runs on an empty stack, and the
background restarts; `restore` puts the unit-scope state back as it was when the background
started (the top-level `catch`); `perCheck` gives every check its own copy of the unit-scope state
from the namer, published only by a full check that completes. -/
structure Mode where
  abort : Bool := false
  restore : Bool := false
  perCheck : Bool := false
  /-- Diagnostics a completer produced stay with the facts: a restore keeps them. -/
  keepDiagnostics : Bool := false
  deriving DecidableEq, Repr

def Mode.nested : Mode := {}
def Mode.abortOnly : Mode := { abort := true }
def Mode.abortRestore : Mode := { abort := true, restore := true }
def Mode.abortRestoreKeep : Mode := { abort := true, restore := true, keepDiagnostics := true }
def Mode.abortPerCheck : Mode := { abort := true, perCheck := true }

/-- The unit-scope state a check may consume: what the top-level catch restores. -/
structure Snapshot where
  units : List UnitSt
  scopeSynth : List (Ref × String)
  synthesized : List (Ref × List String)
  gens : List (String × Nat)

/-- The kernel's state: the units, the run's store of facts, the synthetic methods entered into
scopes by bursts, the `SynthesizedMethods` attachments, the implicit factories' generations (a new
symbol is a new generation), `interruptsEnabled`, the targeted check's target, and the scheduler
(`Core.Scheduler`): the safepoint count, the one to fire at, the event, the queue, the answers. -/
structure KSt where
  policy : Policy
  mode : Mode := {}
  snapshot : Option Snapshot := none
  units : List UnitSt := []
  store : Store Fact Value := fun _ => none
  scopeSynth : List (Ref × String) := []
  synthesized : List (Ref × List String) := []
  gens : List (String × Nat) := []
  interruptsEnabled : Bool := true
  target : Option Target := none
  inBackground : Bool := false
  count : Nat := 0
  fireAt : Option Nat := none
  fired : Bool := false
  event : Option Event := none
  queue : List Event := []
  answers : List Answer := []
  trace : List String := []

/-- Exceptions over state, so that a `TyperResult` keeps what the abandoned check did to the state:
that is the whole point. -/
abbrev K := ExceptT Exc (StateM KSt)

/-! ## Forcing a fact, with the facts it completed -/

/-- `forcePeek` that also returns the facts it completed, in completion order (each is a safepoint
inside a completer, the toy's `signalDone` after a member's right-hand side), and, on a cyclic
reference, the stack of facts in progress, innermost first: scalac gives each of them an error
type as the error propagates as a value, and each ends with its safepoint. -/
abbrev LogOut := Out Fact Value × Store Fact Value × List Fact × List Fact

def runLog (stk : List Fact) (f : Store Fact Value → Fact → LogOut) :
    Task (Probe Fact) (fun _ => Value) Value → Store Fact Value → LogOut
  | .pure v, s => (.ok v, s, [], [])
  | .ask (.peek q) k, s =>
    if q ∈ stk then runLog stk f (k absent) s
    else match f s q with
      | (.ok v, s', l, _) => match runLog stk f (k v) s' with | (o, s'', l', c) => (o, s'', l ++ l', c)
      | (e, s', l, c) => (e, s', l, c)
  | .ask (.force q) k, s =>
    match f s q with
    | (.ok v, s', l, _) => match runLog stk f (k v) s' with | (o, s'', l', c) => (o, s'', l ++ l', c)
    | (e, s', l, c) => (e, s', l, c)

def forceLog (R : PRules Fact Value) : Nat → List Fact → Store Fact Value → Fact → LogOut
  | 0, _, s, _ => (.fuel, s, [], [])
  | n + 1, stk, s, q =>
    match s q with
    | some v => (.ok v, s, [], [])
    | none =>
      if q ∈ stk then (.cyc q, s, [], stk)
      else
        match runLog (q :: stk) (fun s' q' => forceLog R n (q :: stk) s' q') (R q) s with
        | (.ok v, s', l, _) => (.ok v, upd s' q v, l ++ [q], [])
        | (e, s', l, c) => (e, s', l, c)

/-! ## Small helpers -/

def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sorted : List String → List String
  | [] => []
  | x :: xs => insertSorted x (sorted xs)

def sortedSet (l : List String) : List String := sorted l.eraseDups


def showTy : Ty → String
  | .ref r => r.name
  | .builtin n => n
  | .err m => s!"<error: {m}>"

def bodyKey (d : Decl) : String := (if d.obj then "object " else if d.isCase then "class " else "class ") ++ d.name

def refKey (r : Ref) : String := (if r.obj then "object " else "class ") ++ r.name

def addTo (key : String) (name : String) (bodies : List (String × List String)) : List (String × List String) :=
  match bodies.find? (·.1 == key) with
  | some _ => bodies.map fun (k, b) => if k == key then (k, b ++ [name]) else (k, b)
  | none => bodies ++ [(key, [name])]

def bodyOf (key : String) (bodies : List (String × List String)) : List String :=
  ((bodies.find? (·.1 == key)).map (·.2)).getD []

/-! ## State access -/

def prog : K Program := do return (← get).units.flatMap (·.decls)

def getUnit (f : String) : K (Option UnitSt) := do return (← get).units.find? (·.name == f)

def modUnit (f : String) (g : UnitSt → UnitSt) : K Unit :=
  modify fun st => { st with units := st.units.map fun u => if u.name == f then g u else u }

/-- The unit that declares `r`. -/
def unitOf (r : Ref) : K String := do
  let st ← get
  return ((st.units.find? fun u => (findDecl u.decls r).isSome).map (·.name)).getD "?"

def gen (i : String) : K Nat := do return (((← get).gens.find? (·.1 == i)).map (·.2)).getD 0

def setGen (i : String) (n : Nat) : K Unit :=
  modify fun st => { st with gens := (i, n) :: st.gens.filter (·.1 != i) }

/-! ## Warnings and problems -/

def warn (f : String) (decl member msg : String) : K Unit := do
  let p : Problem := ⟨"warning", f, decl, member, msg⟩
  let some u ← getUnit f | pure ()
  if u.suppressionsKnown then
    (if decl ∈ u.suppressions then pure () else modUnit f fun u => { u with problems := u.problems ++ [p] })
  else modUnit f fun u => { u with suspended := u.suspended ++ [p] }

def problem (f : String) (decl member msg : String) : K Unit :=
  modUnit f fun u => { u with problems := u.problems ++ [⟨"error", f, decl, member, msg⟩] }

/-- `reportSuspendedMessages`. -/
def reportSuspended (f : String) : K Unit :=
  modUnit f fun u =>
    { u with problems := u.problems ++ u.suspended.filter (fun p => p.decl ∉ u.suppressions),
             suspended := [], suppressionsKnown := true }

/-! ## The implicit cache -/

/-- `implicitss`, cached for the run on first use: the implicit classes with their factories'
generations. -/
def implicitCandidates (f : String) : K (List (String × Nat)) := do
  let some u ← getUnit f | return []
  match u.implicitCache with
  | some c => return c
  | none =>
    let p ← prog
    let mut c := []
    for d in p do
      if d.isImplicit && !d.obj then c := c ++ [(d.name, ← gen d.name)]
    modUnit f fun u => { u with implicitCache := some c }
    return c

/-- A cached candidate whose factory the name no longer resolves to is shadowed. -/
def shadowed (f : String) (i : String) : K Bool := do
  let c ← implicitCandidates f
  let g ← gen i
  return (c.find? (·.1 == i)).map (·.2) != some g

/-! ## Safepoints and servicing -/

/-- `signalDone`: count the safepoint, inject the harness's event if this is the one, and, if
requests may be serviced here, finish a targeted check that reached its target, then `pollForWork`. -/
def signalDone (nested : Ask → K Answer) (f : String) (where_ : String) (reached : Option Target) (serviceable : Bool)
    (poll : (Ask → K Answer) → K Unit) (completion : String → Target → K Answer) : K Unit := do
  let st ← get
  let k := st.count
  modify fun st => { st with count := k + 1, trace := st.trace ++ [where_] }
  if st.fireAt == some k && !st.fired then
    match st.event with
    | some e => modify fun st => { st with fired := true, queue := st.queue ++ [e] }
    | none => pure ()
  let st ← get
  if st.mode.abort then
    -- a request is waiting and nothing masks cancellation: unwind the background check
    if st.inBackground && !st.queue.isEmpty && st.interruptsEnabled then throw .cancelled
    if !serviceable || !st.interruptsEnabled then return
    match reached, st.target with
    | some t, some t' => if t == t' then throw (.typerResult (← completion f t))
    | _, _ => pure ()
    return
  if !serviceable || !st.interruptsEnabled then return
  match reached, st.target with
  | some t, some t' => if t == t' then throw (.typerResult (← completion f t))
  | _, _ => pure ()
  poll nested

def uninterruptible (op : K Unit) : K Unit := do
  let saved := (← get).interruptsEnabled
  modify fun st => { st with interruptsEnabled := false }
  let r ← tryCatch (do op; pure none) (fun e => pure (some e))
  modify fun st => { st with interruptsEnabled := saved }
  match r with
  | some e => throw e
  | none => pure ()

/-! ## Answers -/

/-- The members of a class as the kernel's scope has them: the source's, the synthetic methods a
burst entered, and the parents'. -/
def memberNamesK (p : Program) (scopeSynth : List (Ref × String)) : Nat → Ref → List String
  | 0, _ => []
  | fuel + 1, r =>
    let own := match findDecl p r with
      | none => []
      | some d => (if d.isCase && !d.obj then d.params.map (·.1) else []) ++ d.members.map (·.name)
    let synth := scopeSynth.filterMap fun (r', n) => if r' == r then some n else none
    let apply := if r.obj && isCaseClass p r.name then ["apply", "unapply"] else if !r.obj && isCaseClass p r.name then ["copy"] else []
    let inherited := match (findDecl p r).bind (·.parent) with
      | some par => memberNamesK p scopeSynth fuel (cls par)
      | none => []
    (own ++ synth ++ apply ++ inherited).eraseDups

/-- `completionAnswer`: the members of the target member's type, with the implicit views that
are not shadowed. -/
def completionAnswer (f : String) (t : Target) : K Answer := do
  let p ← prog
  let st ← get
  let r := if (findDecl p (cls t.decl)).isSome then cls t.decl else obj t.decl
  match st.store (.mem r t.member) with
  | some (.typed ty) =>
    match ty.ty with
    | .ref c =>
      let mut names := memberNamesK p st.scopeSynth p.length c
      for (i, _) in ← implicitCandidates f do
        if !(← shadowed f i) then
          match findDecl p (cls i) with
          | some d =>
            if d.params.head?.map (·.2) == some c.name then
              for n in memberNamesK p st.scopeSynth p.length (cls i) do
                if n ∉ names then names := names ++ [s!"{n} via {i}"]
          | none => pure ()
      return .completion c.name (sortedSet names)
    | other => return .completion (showTy other) ["<no members>"]
  | _ => return .text s!"<no such member {t.member}>"

/-- `unitAnswer`: each declaration's typed body, the synthetic companions, and the problems. -/
def unitAnswer (f : String) : K Answer := do
  let some u ← getUnit f | return .text "<no such file>"
  let mut bodies := []
  let mut printed := []
  for d in u.decls do
    let key := bodyKey d
    printed := printed ++ [key]
    bodies := bodies ++ [(key, sortedSet (bodyOf key u.bodies))]
  let top := bodyOf "<toplevel>" u.bodies
  if !top.isEmpty then bodies := bodies ++ [("synthetic companions", sortedSet top)]
  for (k, b) in u.bodies do
    if k ∉ printed && k != "<toplevel>" then bodies := bodies ++ [(k ++ " (synthetic)", sortedSet b)]
  return .loaded bodies (sortedSet (u.problems.map Problem.render))

/-! ## Forcing a member's type -/

/-- What follows a completed member type (the end of `memberCompleter`): its deprecation
warnings, its error if any, the shadowed-implicit check, and the safepoint inside the completer,
which counts but services nothing (`lockedCount > 0`). -/
def afterCompleted (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (o : Ref) (m : String) : K Unit := do
  let f ← unitOf o
  let st ← get
  match st.store (.mem o m) with
  | some (.typed t) =>
    for (owner, n) in t.deprecated do warn f o.name m s!"method {n} in {owner.name} is deprecated"
    match t.via with
    | some v => if ← shadowed f v.cls then problem f o.name m s!"value {v.member} is not a member of {v.onType}"
    | none => pure ()
    match t.ty with
    | .err msg => problem f o.name m msg
    | _ => pure ()
  | _ => pure ()
  signalDone nested f s!"rhs {o.name}.{m}" none false poll completionAnswer

def forceMember (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (r : Ref) (n : String) : K Unit := do
  let p ← prog
  let st ← get
  let (out, store', log, cycStack) := forceLog (rulesOf .scalac p) 40 [] st.store (.mem r n)
  modify fun st => { st with store := store' }
  for q in log do
    match q with
    | .mem o m => afterCompleted nested poll o m
    | _ => pure ()
  match out with
  | .cyc q =>
    -- every completer on the stack ends with the error as its value (`CyclicReference` caught in
    -- `typePath`, then an error type), innermost first, each with its safepoint
    let msg := s!"cyclic reference involving {match q with | .mem _ m => m | .decls c => c.name | .info c => c.name}"
    for f in cycStack do
      match f with
      | .mem o m =>
        modify fun st => { st with store := upd st.store (.mem o m) (ty (.err msg)) }
        afterCompleted nested poll o m
      | _ => pure ()
  | _ => pure ()

/-! ## The typer -/

def synthNames : List String := ["equals", "hashCode", "toString"]

/-- `addSyntheticMethods` for a case class. -/
def finishMethodSynthesis (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (f : String) (r : Ref) (body : List String) :
    K (List String) := do
  let st ← get
  if st.policy.idempotentSynthetics then
    let mut body := body
    for n in synthNames do
      if (r, n) ∉ (← get).scopeSynth then modify fun st => { st with scopeSynth := st.scopeSynth ++ [(r, n)] }
      body := body ++ [n]
      signalDone nested f s!"synth {r.name}.{n}" none true poll completionAnswer
    return body
  if (r, "equals") ∈ st.scopeSynth then
    match st.synthesized.find? (·.1 == r) with
    | some (_, names) =>
      if st.target.isNone then modify fun st => { st with synthesized := st.synthesized.filter (·.1 != r) }
      return body ++ names
    | none => return body
  let mut body := body
  for n in synthNames do
    modify fun st => { st with scopeSynth := st.scopeSynth ++ [(r, n)] }
    body := body ++ [n]
    signalDone nested f s!"synth {r.name}.{n}" none true poll completionAnswer
  if st.target.isSome && st.policy.keepSyntheticsForTargeted then
    modify fun st => { st with synthesized := st.synthesized ++ [(r, synthNames)] }
  return body

/-- `addSynthetics`: the trees from declaration `pos` join their owner's body. -/
def addSynthetics (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (f : String) (pos : Nat)
    (bodies : List (String × List String)) : K (List (String × List String)) := do
  let some u ← getUnit f | return bodies
  let st ← get
  let mut bodies := bodies
  for (key, name, origin) in u.synthetics do
    if origin != pos then continue
    if st.policy.idempotentSynthetics then
      if name ∈ bodyOf key bodies then continue
    else if st.target.isNone || !st.policy.keepSyntheticsForTargeted then
      modUnit f fun u => { u with synthetics := u.synthetics.filter fun (k, n, o) => !(k == key && n == name && o == origin) }
    bodies := addTo key name bodies
    signalDone nested f s!"synthetic {key}.{name}" none true poll completionAnswer
  return bodies

/-- `enterImplicitWrapper`, each time the template is typed (the namer entered the first factory
at the run's start): a new factory (generation) unless kept. -/
def enterImplicitWrapper (f : String) (d : Decl) (pos : Nat) : K Unit := do
  let g ← gen d.name
  if !(← get).policy.keepFactory then setGen d.name (g + 1)
  modUnit f fun u =>
    if u.synthetics.any (fun (k, n, _) => k == "<toplevel>" && n == d.name) then u
    else { u with synthetics := u.synthetics ++ [("<toplevel>", d.name, pos)] }

def typeDecl (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (f : String) (d : Decl) (pos : Nat)
    (bodies : List (String × List String)) : K (List (String × List String)) := do
  let r := if d.obj then obj d.name else cls d.name
  if d.isImplicit then enterImplicitWrapper f d pos
  let mut body := if d.isCase && !d.obj then d.params.map (·.1) else []
  for m in d.members do
    forceMember nested poll r m.name
    body := body ++ [m.name]
    signalDone nested f s!"member {d.name}.{m.name}" (some ⟨d.name, m.name⟩) true poll completionAnswer
  if d.nowarn then modUnit f fun u => { u with suppressions := u.suppressions ++ [d.name] }
  if d.isCase && !d.obj then
    let pol := (← get).policy
    if pol.uninterruptibleSynthesis then
      let saved := (← get).interruptsEnabled
      modify fun st => { st with interruptsEnabled := false }
      let r' ← tryCatch (do let b ← finishMethodSynthesis nested poll f r body; pure (Sum.inl b)) (fun e => pure (Sum.inr e))
      modify fun st => { st with interruptsEnabled := saved }
      match r' with
      | .inl b => body := b
      | .inr e => throw e
    else body := ← finishMethodSynthesis nested poll f r body
  let bodies := bodies ++ [(bodyKey d, body)]
  signalDone nested f s!"class {d.name}" none true poll completionAnswer
  return bodies

def typeDecls (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (f : String) :
    List (Decl × Nat) → List (String × List String) → K (List (String × List String))
  | [], bodies => pure bodies
  | (d, pos) :: ds, bodies => do
    let bodies ← typeDecl nested poll f d pos bodies
    let pol := (← get).policy
    let bodies ←
      if pol.uninterruptibleSynthesis then do
        let saved := (← get).interruptsEnabled
        modify fun st => { st with interruptsEnabled := false }
        let r ← tryCatch (do let b ← addSynthetics nested poll f pos bodies; pure (Sum.inl b)) (fun e => pure (Sum.inr e))
        modify fun st => { st with interruptsEnabled := saved }
        match r with
        | .inl b => pure b
        | .inr e => throw e
      else addSynthetics nested poll f pos bodies
    typeDecls nested poll f ds bodies

/-- `typeUnit`: the declarations in order; a targeted check unwinds at its target with the
completion. -/
def typeUnit (nested : Ask → K Answer) (poll : (Ask → K Answer) → K Unit) (f : String) (target : Option Target) : K Unit := do
  let some u ← getUnit f | return
  if (← get).mode.perCheck then
    modUnit f fun u => { u with synthetics := u.synthetics0, suspended := [], suppressions := [], suppressionsKnown := false, implicitCache := none }
  let saved := (← get).target
  modify fun st => { st with target := target }
  let r ← tryCatch (do let b ← typeDecls nested poll f (u.decls.zipIdx) []; pure (Sum.inl b)) (fun e => pure (Sum.inr e))
  let pol := (← get).policy
  match r with
  | .inl bodies => do
    if target.isNone then
      reportSuspended f
      modUnit f fun u => { u with bodies := bodies, typed := true }
    else if !pol.suspendTargetedWarnings then reportSuspended f
    modify fun st => { st with target := saved }
  | .inr e => do
    match e with
    | .typerResult _ => if !pol.suspendTargetedWarnings then reportSuspended f
    | .cancelled => pure ()
    modify fun st => { st with target := saved }
    throw e

/-! ## Runs, requests, the background -/

/-- A new run (`newRun`): fresh facts, scopes and generations; the units' synthetic trees as the
namer leaves them (a case class's companion if it has none, with `apply` and `unapply`, and its
`copy`), and the implicit factories at their first generation. -/
def newRun (units : List (String × Program)) : K Unit :=
  modify fun st =>
    { st with
      store := fun _ => none, scopeSynth := [], synthesized := [],
      gens := (units.flatMap (·.2)).filterMap fun d => if d.isImplicit && !d.obj then some (d.name, 1) else none,
      units := units.map fun (name, decls) =>
        let synth := (decls.zipIdx).flatMap fun (d, pos) =>
          if d.isCase && !d.obj then
            (if decls.any (fun o => o.obj && o.name == d.name) then [] else [("<toplevel>", d.name, pos)]) ++
              [("object " ++ d.name, "apply", pos), ("object " ++ d.name, "unapply", pos), ("class " ++ d.name, "copy", pos)]
          else []
        { name, decls, synthetics := synth, synthetics0 := synth } }

def reload (file : String) (text : Program) : K Unit := do
  let st ← get
  newRun (st.units.map fun u => (u.name, if u.name == file then text else u.decls))

/-- `pollForWork`: service the queue; an edit is a new run, which abandons a background check. -/
def pollForWorkFuel (nested : Ask → K Answer) : Nat → K Unit
  | 0 => pure ()
  | fuel + 1 => do
    let st ← get
    match st.queue with
    | [] => pure ()
    | e :: rest =>
      modify fun st => { st with queue := rest }
      match e with
      | .edit f text a =>
        reload f text
        modify fun st => { st with queue := .request a :: st.queue }
        if (← get).inBackground then throw .cancelled
      | .request a =>
        let ans ← nested a
        modify fun st => { st with answers := st.answers ++ [ans] }
      pollForWorkFuel nested fuel

def pollForWork (nested : Ask → K Answer) : K Unit := pollForWorkFuel nested 8

/-- `serve` with `nested` for the requests serviced inside this one. -/
def serveWith (nested : Ask → K Answer) : Ask → K Answer
  | .completion f d m => do
    let some u ← getUnit f | return .text "<no such file>"
    if u.typed then completionAnswer f ⟨d, m⟩
    else
      let r ← tryCatch (do typeUnit nested pollForWork f (some ⟨d, m⟩); pure none) (fun e => pure (some e))
      match r with
      | none => return .text "<target not reached>"
      | some (.typerResult a) => return a
      | some .cancelled => throw .cancelled
  | .loadedTyped f => do
    let some u ← getUnit f | return .text "<no such file>"
    if !u.typed then typeUnit nested pollForWork f none
    unitAnswer f

/-- Requests nest to a depth: a request serviced inside a request inside the background. -/
def serve : Nat → Ask → K Answer
  | 0, _ => pure (.text "<depth>")
  | d + 1, a => serveWith (serve d) a

def backgroundCompile (nested : Ask → K Answer) : K Unit := do
  let st ← get
  for u in st.units do
    if !u.typed then typeUnit nested pollForWork u.name none

/-- `drain`: the background to completion, restarted after each `FreshRunReq`, then the queue. -/
def takeSnapshot : K Unit :=
  modify fun st => { st with snapshot := some ⟨st.units, st.scopeSynth, st.synthesized, st.gens⟩ }

/-- The top-level `catch`: the unit-scope state as the background found it; a unit a request has
since fully typed stays typed. -/
def restoreSnapshot : K Unit :=
  modify fun st => match st.snapshot with
    | some sn =>
      let units := sn.units.map fun u =>
        match st.units.find? (·.name == u.name) with
        | some cur =>
          if cur.typed && !u.typed then cur
          else if st.mode.keepDiagnostics then { u with problems := cur.problems, suspended := cur.suspended }
          else u
        | none => u
      { st with units, scopeSynth := sn.scopeSynth, synthesized := sn.synthesized, gens := sn.gens }
    | none => st

def drain : Nat → K Unit
  | 0 => pure ()
  | fuel + 1 => do
    let r ← tryCatch
      (do pollForWork (serve 3)
          takeSnapshot
          modify fun st => { st with inBackground := true }
          backgroundCompile (serve 3); modify fun st => { st with inBackground := false }; pure true)
      (fun e => match e with
        | .cancelled => do
          modify fun st => { st with inBackground := false }
          if (← get).mode.restore then restoreSnapshot
          pure false
        | .typerResult _ => pure true)
    if r then pollForWork (serve 3) else drain fuel

/-! ## The harness -/

structure Scenario where
  name : String
  units : List (String × Program)
  event : Event

def runK (st : KSt) (m : K Unit) : KSt := (m.run.run st).2

def fresh (policy : Policy) (sc : Scenario) (fireAt : Option Nat) (mode : Mode := {}) : KSt :=
  { policy, mode, fireAt, event := some sc.event }

/-- The background with the event injected at safepoint `fireAt` (or never). -/
def background (policy : Policy) (sc : Scenario) (fireAt : Option Nat) (mode : Mode := {}) : KSt :=
  runK (fresh policy sc fireAt mode) (do newRun sc.units; drain 6)

def safepoints (policy : Policy) (sc : Scenario) (mode : Mode := {}) : Nat := (background policy sc none mode).count

def backgroundTrace (policy : Policy) (sc : Scenario) (mode : Mode := {}) : List String := (background policy sc none mode).trace

/-- After the background: the event if it was not fired, then a `loadedTyped` of every unit. -/
def finish (sc : Scenario) (st : KSt) : List Answer :=
  (runK st (do
    if !st.fired then modify fun st => { st with queue := st.queue ++ [sc.event] }
    drain 6
    for (f, _) in sc.units do
      modify fun st => { st with queue := st.queue ++ [.request (.loadedTyped f)] }
      drain 6)).answers

def reference (policy : Policy) (sc : Scenario) (mode : Mode := {}) : List Answer := finish sc (background policy sc none mode)

def atSafepoint (policy : Policy) (sc : Scenario) (k : Nat) (mode : Mode := {}) : List Answer := finish sc (background policy sc (some k) mode)

/-- The safepoints at which injecting the event changes an answer. -/
def divergent (policy : Policy) (sc : Scenario) (mode : Mode := {}) : List Nat :=
  let ref := reference policy sc mode
  (List.range (safepoints policy sc mode)).filter fun k => atSafepoint policy sc k mode != ref

/-! ## The scenarios of `probes/interrupt/scenarios`, and `results.txt` as theorems -/

def intD : Decl := { name := "Int" }
def m (name : String) (declared : String) : Stat := .member { name, declared := some declared }
def inf (name : String) (path : List String) : Stat := .member { name, path }

/-- `case-class-completion.toy`: a completion of a case class's members during its synthesis. -/
def caseClassCompletion : Scenario :=
  { name := "case-class-completion",
    units := [("A", [intD,
      { isCase := true, name := "L", params := [("a", "Int")], stats := [m "self" "L"] },
      { obj := true, name := "Use", stats := [m "l" "L", inf "f" ["l", "self"]] }])],
    event := .request (.completion "A" "Use" "f") }

/-- `case-class-loaded.toy`: a whole-unit request during the background check of the unit. -/
def caseClassLoaded : Scenario := { caseClassCompletion with name := "case-class-loaded", event := .request (.loadedTyped "A") }

/-- `cycle.toy`. -/
def cycleSc : Scenario :=
  { name := "cycle",
    units := [("A", [intD,
      { name := "C", stats := [inf "a" ["b"], inf "b" ["a"], m "c" "Int", inf "p" ["q", "c"], m "q" "C"] }])],
    event := .request (.completion "A" "C" "p") }

/-- `edit-cross-file.toy`: an edit of `B` while `A`, which reads `B`, is typed. -/
def editCrossFile : Scenario :=
  { name := "edit-cross-file",
    units := [("A", [intD, { name := "A", stats := [inf "y" ["B", "x"], inf "z" ["B", "w"]] }]),
              ("B", [{ obj := true, name := "B", stats := [m "x" "Int", m "w" "Int"] }])],
    event := .edit "B" [{ obj := true, name := "B", stats := [m "x" "Int", m "w" "A"] }] (.loadedTyped "A") }

/-- `implicit-class.toy`. -/
def implicitClass : Scenario :=
  { name := "implicit-class",
    units := [("A", [intD,
      { name := "Before", stats := [m "x" "Int"] },
      { isImplicit := true, name := "RichInt", params := [("i", "Int")], stats := [m "twice" "Int"] },
      { obj := true, name := "Use", stats := [m "b" "Before", inf "f" ["b", "x"], m "three" "Int", inf "g" ["three", "twice"]] }])],
    event := .request (.completion "A" "Use" "f") }

/-- `nowarn.toy`. -/
def nowarnSc : Scenario :=
  { name := "nowarn",
    units := [("A", [intD,
      { name := "Old", stats := [.member { name := "m", declared := some "Int", deprecated := true }] },
      { obj := true, name := "Use", stats := [m "o" "Old", inf "foo" ["o", "m"]] },
      { obj := true, nowarn := true, name := "Later", stats := [m "o" "Old", inf "bar" ["o", "m"]] }])],
    event := .request (.completion "A" "Use" "foo") }

/-- `targeted-consumes-synthetics.toy`. -/
def targetedConsumes : Scenario :=
  { name := "targeted-consumes-synthetics",
    units := [("A", [intD,
      { name := "Before", stats := [m "x" "Int"] },
      { isCase := true, name := "L", params := [("a", "Int")] },
      { obj := true, name := "Use", stats := [m "l" "L", inf "f" ["l", "a"]] }])],
    event := .request (.completion "A" "Use" "f") }

def scenarios : List Scenario :=
  [caseClassCompletion, caseClassLoaded, cycleSc, editCrossFile, implicitClass, nowarnSc, targetedConsumes]

/-! ### Abort and restart

The same scenarios with a request *aborting* the background check at its safepoint instead of
being serviced inside it. The theorems are the obligations of track-i.md §11, one per bit of
cleanup. -/

/-- **Idempotent synthetics make abort safe with no cleanup at all**: under the proposal, with no
restore, no scenario diverges at any safepoint. -/
theorem abort_proposed_safe :
    scenarios.map (fun sc => divergent .proposed sc .abortOnly) = scenarios.map (fun _ => []) := by
  decide +kernel

/-- **Consumed maps and the burst are not resumable**: under the PR's policy, an abort after the
burst has begun (safepoint 3) or after synthetic trees were consumed leaves the restart short. -/
theorem abort_after_not_resumable :
    divergent .after caseClassLoaded .abortOnly = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] ∧
    divergent .after caseClassCompletion .abortOnly = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
  decide +kernel

/-- **A top-level restore repairs them**, and loses the diagnostics: the warning `Use.foo`
emitted when its type was completed is wiped by the restore and never re-emitted, since the fact is
memoized; the cyclic-reference errors likewise, under every policy. -/
theorem abort_restore_loses_diagnostics :
    divergent .after caseClassLoaded .abortRestore = [] ∧
    divergent .after nowarnSc .abortRestore = [6, 7, 8, 9, 10, 11, 12, 13] ∧
    divergent .proposed cycleSc .abortRestore = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  decide +kernel

/-- **Diagnostics kept with the facts close the last gap**: restore everything but what the
completers reported, and nothing diverges under the PR's policy or the proposal. -/
theorem abort_restore_keep_safe :
    scenarios.map (fun sc => divergent .after sc .abortRestoreKeep) = scenarios.map (fun _ => []) ∧
    scenarios.map (fun sc => divergent .proposed sc .abortRestoreKeep) = scenarios.map (fun _ => []) := by
  decide +kernel

/-- The kernel's safepoints are the Java kernel's, by name and in order (`results.txt`, `--trace`). -/
theorem caseClassCompletion_trace :
    backgroundTrace .before caseClassCompletion =
      ["class Int", "rhs L.self", "member L.self", "synth L.equals", "synth L.hashCode", "synth L.toString", "class L",
       "synthetic <toplevel>.L", "synthetic object L.apply", "synthetic object L.unapply", "synthetic class L.copy",
       "rhs Use.l", "member Use.l", "rhs Use.f", "member Use.f", "class Use"] := by
  decide +kernel

/-- **`results.txt` is a theorem.** For each scenario: the background's safepoints, and the
divergent ones under the policy before scala/scala#11328, after it, and the proposal. -/
theorem results_before_after_proposed :
    scenarios.map (fun sc => (sc.name, safepoints .before sc, divergent .before sc, divergent .after sc, divergent .proposed sc)) =
      [("case-class-completion", 16, List.range 7, [], []),
       ("case-class-loaded", 16, List.range 16, List.range 16, []),
       ("cycle", 12, [], [], []),
       ("edit-cross-file", 11, [], [], []),
       ("implicit-class", 17, [0, 1, 2, 3, 4, 5, 6, 14, 15, 16], [], []),
       ("nowarn", 14, List.range 13, [], []),
       ("targeted-consumes-synthetics", 18, List.range 8, [], [])] := by
  decide +kernel

end ScalaTypes.ToyKernel
