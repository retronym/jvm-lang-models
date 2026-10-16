import Zinc.Bridges.FlatRules
import Zinc.Features.Erasure
import Zinc.Features.ImplicitScope
import Zinc.Loop.PingPong
import Zinc.Bridges.HierShared
import Zinc.Bridges.FlatShared
import Lean.Data.Json
/-! Runs the bounded exhaustive checks as native code.

* `exhaustive [N]`: `packages/zinc/Zinc/Bridges/FlatRules.lean`, for every rule set the number of unclean (base, edit)
  pairs and the smallest one. `N` checks the first `N` bases only. Chunks of bases are checked in
  parallel.
* `exhaustive precision [N] [every K]`: the same space (every `K`-th of the first `N` bases), for
  each preset the classes recompiled beyond the edited one against the necessary classes
  (`FlatRules.necessaryOf`): the over-invalidation table, cumulative after each tenth of the
  bases, with two concrete (base, edit) samples per batch and every preset's outcome on them.
  With `PRECISION_LOG=file`, one JSON line per batch for a replay.
* `exhaustive v`: the value-class space of `packages/zinc/Zinc/Bridges/FlatRules.lean`.
* `exhaustive flatshared`: `packages/zinc/Zinc/Bridges/FlatShared.lean`, where `Flat`'s linearization,
  selections and refchecks agree with the shared Scala semantics, over `FlatRules`' programs.
* `exhaustive erasure [N]`: `packages/zinc/Zinc/Features/Erasure.lean`, for every rendering the unclean runs and the
  wasted recompiles, per class.
* `exhaustive implicit`: `packages/zinc/Zinc/Features/ImplicitScope.lean`, for every variant the unclean runs, the
  wasted recompiles, and the client recompiles against the in-project fallback. -/


section rules
open Zinc.Flat

/-- The rule sets checked: name, recorded key kinds, `abstractAll`, rules. -/
def ruleSets : List (String × (Kind → Bool) × Bool × List Rule) :=
  [("default (as stated)", clientOnly, false, allRules),
   ("default, abstract widened", clientOnly, true, allRules),
   ("none", clientOnly, false, [])] ++
  allRules.map (fun r => (s!"widened without {repr r}", clientOnly, true, allRules.filter (· != r))) ++
  [("widened, trait narrowed to direct mixins", clientOnly, true,
     allRules.map (fun r => if r == .trait then .traitDirect else r)),
   ("widened, traitDirect blind to private members (no extraHash)", clientOnly, true,
     allRules.map (fun r => if r == .trait then .traitPub else r)),
   ("widened, macro-expansion keys dropped", (· == .client), true, allRules),
   ("widened without header, extends clauses recorded", (fun k => clientOnly k || k == .extends),
     true, allRules.filter (· != .header)),
   ("widened without uses, self-uses recorded as keys", (fun k => clientOnly k || k == .uses), true,
     allRules.filter (· != .uses))]

abbrev Bad := List (Cfg × Cfg × Zinc.Hier.Cls)

def checkChunk (bases : List Cfg) : Array Bad := Id.run do
  let mut bad : Array Bad := ruleSets.toArray.map fun _ => []
  for k in bases do
    for (k', e) in edits k do
      let mut j := 0
      for (_, E, ab, rs) in ruleSets do
        if !cleanRun E ab rs (init E k.src) k' e then bad := bad.modify j ((k, k', e) :: ·)
        j := j + 1
  return bad

def chunks (n : ℕ) : List Cfg → ℕ → List (List Cfg)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunks n (l.drop n) fuel

/-- The value-class space's rule sets. -/
def ruleSetsV : List (String × (Kind → Bool) × Bool × List Rule) :=
  [("default, abstract widened", clientOnly, true, allRules),
   ("default + erasure keys (codegen's reads of V recorded)",
     (fun k => clientOnly k || k == .erasure), true, allRules),
   ("none", clientOnly, false, [])] ++
  [Rule.overrides, .trait, .mirror].map (fun r =>
    (s!"+ erasure keys, without {repr r}", (fun k => clientOnly k || k == .erasure), true,
      allRules.filter (· != r)))

def checkChunkV (bases : List CfgV) : Array (List (CfgV × CfgV × Zinc.Hier.Cls)) := Id.run do
  let mut bad : Array (List (CfgV × CfgV × Zinc.Hier.Cls)) := ruleSetsV.toArray.map fun _ => []
  for k in bases do
    for (k', e) in editsV k do
      let mut j := 0
      for (_, E, ab, rs) in ruleSetsV do
        if !cleanRunSrc E ab rs (init E k.src) k'.src e then bad := bad.modify j ((k, k', e) :: ·)
        j := j + 1
  return bad

def chunksV (n : ℕ) : List CfgV → ℕ → List (List CfgV)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunksV n (l.drop n) fuel

def mainV : IO Unit := do
  IO.println s!"{cfgsV.length} value-class bases, {(cfgsV.flatMap editsV).length} edits"
  (← IO.getStdout).flush
  let results := ((chunksV 100 cfgsV cfgsV.length).map fun ch => Task.spawn fun _ => checkChunkV ch).map Task.get
  let mut j := 0
  for (name, _, _, _) in ruleSetsV do
    let l := results.flatMap fun r => r[j]!
    IO.println s!"{name}: {l.length} unclean"
    match l.head? with
    | some (k, k', e) => IO.println s!"  base {repr k}\n  edit {repr e} → {repr k'}"
    | none => pure ()
    j := j + 1

def mainRules (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  (← IO.getStdout).flush
  let tasks := (chunks 500 bases bases.length).map fun ch => Task.spawn fun _ => checkChunk ch
  let results := tasks.map Task.get
  let mut j := 0
  for (name, _, _, _) in ruleSets do
    let l := results.flatMap fun r => r[j]!
    IO.println s!"{name}: {l.length} unclean"
    match minimal l with
    | some (k, k', e) => IO.println s!"  base {repr k}\n  edit {repr e} → {repr k'}"
    | none => pure ()
    j := j + 1

/-- Per preset, the precision counts over a chunk of bases. The necessary set is computed once per
(base, edit) and shared by the presets. -/
def precChunk (bases : List Cfg) : Array Prec := Id.run do
  let mut acc : Array Prec := presets.toArray.map fun _ => {}
  for k in bases do
    let s₀ := init clientOnly k.src
    for (k', e) in edits k do
      let nec := necessaryOf k.src k'.src s₀ e
      let mut j := 0
      for (_, E, ab, rs) in presets do
        acc := acc.modify j (·.add (precRun E ab rs (init E k.src) nec k'.src e))
        j := j + 1
  return acc

/-- `precision why [N]`: for the `default, traitDirect` preset, the first few (base, edit, class)
where a class is necessary by its trace and not recompiled, with the changed queries. -/
def mainPrecisionWhy (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 200
  let (_, E, ab, rs) := presets[3]!
  let mut shown := 0
  let mut byKind : List (String × ℕ) := []
  for k in cfgs.take n do
    let s₀ := init E k.src
    for (k', e) in edits k do
      let nec := necessaryOf k.src k'.src s₀ e
      match runF E .zinc k'.src (rulePolicy k'.src ab rs) 9 0 ∅ {e} s₀ with
      | none => pure ()
      | some r =>
        for c in nec do
          if c ∉ r.compiled then
            let qs := changedQueries k.src k'.src s₀ c
            for (p, q, _, _) in qs do
              let key := s!"{repr q} on {repr p} from {repr c}"
              byKind := match byKind.lookup key with
                | some m => (key, m + 1) :: byKind.filter (·.1 != key)
                | none => (key, 1) :: byKind
            if shown < 6 then
              shown := shown + 1
              IO.println s!"base {repr k}\n  edit {repr e} → {repr k'}\n  {repr c} necessary, not recompiled; changed: {repr qs}"
  IO.println "by query:"
  for (key, m) in (byKind.toArray.qsort (fun a b => a.2 > b.2)).toList.take 20 do
    IO.println s!"  {m}× {key}"

/-- Every `k`-th element. `cfgs` enumerates its Boolean knobs innermost, in a cycle of 32, so `k`
must be coprime with 32 (a prime such as 23) or the sample never varies some knob: a stride of 20
never picks a base with `A` as a trait. -/
def stride (k : ℕ) (l : List Cfg) : List Cfg :=
  (l.zipIdx.filter fun (_, i) => i % k == 0).map (·.1)

def pct (a b : ℕ) : String :=
  if b == 0 then "-" else
    let t := a * 1000 / b
    s!"{t / 10}.{t % 10}%"

def optTag : Opt → String
  | .none => "-" | .int => "Int" | .str => "String" | .par => "T" | .dfr => "deferred Int"
  | .val => "val Int" | .var => "var Int" | .lzy => "lazy val Int" | .pval => "private val Int"

def hTy : Zinc.Hier.Ty → String
  | .int => "Int" | .string => "String" | .param => "T" | .v => "V"

/-- A configuration as one line of Scala-ish, for the samples. -/
def cfgSrc (k : Cfg) : String :=
  let mem (o : Opt) := if o == .none then "" else s!" m: {optTag o}"
  let aKind := if k.aTrait then "trait" else "abstract class"
  let aPar := (k.aPar.map fun t => s!" extends M[{hTy t}]").getD ""
  let fin := if k.bFinal then "final " else ""
  let uses := if k.bUses then " uses this.m" else ""
  let xDef := if k.xObj then "extends C[Int]" else "{ B.m }"
  let zDef := if k.zObs then "(macro observing C)" else "{ A.m }"
  s!"{aKind} A[T]{aPar} \{{mem k.oA} }; trait M[T] \{{mem k.oM} }; " ++
  s!"{fin}class B extends A[{hTy k.bArg}] \{{mem k.oB}{uses} }; class C extends B with M[Int] \{{mem k.oC} }; " ++
  s!"object X {xDef}; object Y \{ C.m }; object Z {zDef}"

def clsName : Zinc.Hier.Cls → String
  | .A => "A" | .B => "B" | .M => "M" | .C => "C" | .X => "X" | .Y => "Y" | .Z => "Z" | .V => "V"

/-- One preset's outcome on a pair. -/
structure SampleRow where
  preset : String
  recompiled : List String
  rounds : ℕ
  clean : Bool

/-- One (base, edit) pair in full: the programs, the necessary classes, and per preset what was
recompiled and whether the result equals the clean build. Human eyes on the loop's work. -/
structure Sample where
  base : String
  edited : String
  edit : String
  necessary : List String
  unchanged : List String
  rows : List SampleRow

def samplePair (k k' : Cfg) (e : Zinc.Hier.Cls) : Sample := Id.run do
  let s₀ := init withUses k.src
  let nec := necessaryOf k.src k'.src s₀ e
  let unch := all.filter fun c => c != e && clean k'.src c == s₀.out c
  let mut rows : List SampleRow := []
  for (name, E, ab, rs) in presets do
    match runF E .zinc k'.src (rulePolicy k'.src ab rs) 9 0 ∅ {e} (init E k.src) with
    | none => rows := rows ++ [⟨name, [], 0, false⟩]
    | some r =>
      let cl := memo { out := clean k'.src, U := fun _ => ∅ }
      let ok := all.all fun c => r.state.out c == cl.out c
      let rc := all.filter fun c => c ∈ r.compiled ∧ c ≠ e
      rows := rows ++ [⟨name, rc.map clsName, r.rounds, ok⟩]
  return ⟨cfgSrc k, cfgSrc k', clsName e, nec.map clsName, unch.map clsName, rows⟩

def printSample (x : Sample) : IO Unit := do
  IO.println s!"  base: {x.base}"
  IO.println s!"  edit {x.edit}: {x.edited}"
  IO.println s!"  necessary (an answer they read changed): {x.necessary}"
  IO.println s!"  output unchanged by the edit: {x.unchanged}"
  for r in x.rows do
    IO.println s!"    {r.preset}: recompiled {r.recompiled} in {r.rounds} rounds, {if r.clean then "clean" else "UNCLEAN"}"

def jstr (s : String) : String := Lean.Json.str s |>.compress

def Sample.toJson (x : Sample) : Lean.Json :=
  Lean.Json.mkObj [("base", x.base), ("edit", x.edit), ("edited", x.edited),
    ("necessary", Lean.toJson x.necessary), ("unchanged", Lean.toJson x.unchanged),
    ("presets", Lean.Json.arr (x.rows.toArray.map fun r => Lean.Json.mkObj
      [("preset", r.preset), ("recompiled", Lean.toJson r.recompiled), ("rounds", r.rounds),
       ("clean", r.clean)]))]

/-- One event per batch, as a JSON line: the cumulative table and the batch's samples. A replay
can scrub through the file. Written when `PRECISION_LOG` names a file. -/
def logEvent (done total : ℕ) (acc : Array Prec) (samples : List Sample) : IO Unit := do
  match ← IO.getEnv "PRECISION_LOG" with
  | none => pure ()
  | some path =>
    let table := (presets.zip acc.toList).map fun ((name, _, _, _), t) => Lean.Json.mkObj
      [("preset", name), ("unclean", t.unclean), ("recompiled", t.recompiled),
       ("necessary", t.necessary), ("over", t.over), ("outUnchanged", t.outUnchanged)]
    let ev := Lean.Json.mkObj [("done", done), ("total", total),
      ("table", Lean.Json.arr table.toArray), ("samples", Lean.Json.arr (samples.toArray.map (·.toJson)))]
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn ev.compress

/-- Print the cumulative table. -/
def printPrec (done total : ℕ) (acc : Array Prec) : IO Unit := do
  IO.println s!"after {done} of {total} bases:"
  IO.println "| preset | unclean | recompiled | necessary | over-invalidated | of recompiled | output unchanged |"
  IO.println "|---|---|---|---|---|---|---|"
  let mut j := 0
  for (name, _, _, _) in presets do
    let t := acc[j]!
    IO.println s!"| {name} | {t.unclean} | {t.recompiled} | {t.necessary} | {t.over} | {pct t.over t.recompiled} | {t.outUnchanged} |"
    j := j + 1
  (← IO.getStdout).flush

/-- `precision [N] [every K]`: the first `N` bases, every `K`-th of them. The bases go through in
ten batches, each in parallel chunks of 50, and the cumulative table is printed after each batch,
so a long run shows its progress and a partial run is still a sample. -/
def mainPrecision (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let k := match args with
    | _ :: "every" :: k :: _ => k.toNat?.getD 1
    | "every" :: k :: _ => k.toNat?.getD 1
    | _ => 1
  let bases := stride k (cfgs.take n)
  let total := bases.length
  IO.println s!"{total} bases (every {k}th of the first {n}), {(bases.flatMap edits).length} edits"
  (← IO.getStdout).flush
  let batch := max 50 ((total + 9) / 10)
  let mut acc : Array Prec := presets.toArray.map fun _ => {}
  let mut done := 0
  for b in chunks batch bases total do
    let tasks := (chunks 50 b b.length).map fun ch => Task.spawn fun _ => precChunk ch
    for r in tasks.map Task.get do
      acc := (acc.zip r).map fun (a, x) => a.add x
    done := done + b.length
    printPrec done total acc
    let samples : List Sample :=
      match b.head?, (b.drop (b.length / 2)).head? with
      | some k, some k₂ =>
        match (edits k).head?, ((edits k₂).drop ((edits k₂).length / 2)).head? with
        | some (k', e), some (k₂', e₂) =>
          samplePair k k' e :: (if k₂ != k then [samplePair k₂ k₂' e₂] else [])
        | _, _ => []
      | _, _ => []
    IO.println "sample from this batch:"
    for x in samples do printSample x
    logEvent done total acc samples
    (← IO.getStdout).flush

end rules

section erasure
open Zinc.Erasure

structure Tally where
  unclean : ℕ := 0
  noRun : ℕ := 0
  wrong : List (Cls × ℕ) := allCls.map (·, 0)
  wasted : List (Cls × ℕ) := allCls.map (·, 0)
  recompiled : ℕ := 0
  /-- Unclean runs by the class edited. -/
  byEdit : List (Cls × ℕ) := allCls.map (·, 0)
  smallest : Option (Cfg × Cfg × Cls) := none
  deriving Inhabited

def bump (l : List (Cls × ℕ)) (cs : List Cls) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, if cs.contains c then n + 1 else n)

def Tally.add (t : Tally) (k k' : Cfg) (e : Cls) : Option Report → Tally
  | none => { t with noRun := t.noRun + 1 }
  | some r =>
    let bad := !r.wrong.isEmpty
    { t with
      unclean := t.unclean + (if bad then 1 else 0)
      wrong := bump t.wrong r.wrong
      wasted := bump t.wasted r.wasted
      byEdit := if bad then bump t.byEdit [e] else t.byEdit
      recompiled := t.recompiled + r.recompiled.length
      smallest := if !bad then t.smallest else match t.smallest with
        | none => some (k, k', e)
        | some (b, b', _) =>
          if k.size < b.size || (k.size == b.size && k'.size < b'.size) then some (k, k', e)
          else t.smallest }

def cfgStr (k : Cfg) : String := (toString (repr k)).replace "\n" " " |>.replace "Zinc.Erasure." ""

def showCounts (l : List (Cls × ℕ)) : String :=
  ", ".intercalate ((l.filter (·.2 != 0)).map fun (c, n) => s!"{(toString (repr c)).replace "Zinc.Erasure.Cls." ""} {n}")

def mergeCounts (l l' : List (Cls × ℕ)) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, n + ((l'.lookup c).getD 0))

def Tally.merge (t u : Tally) : Tally :=
  { unclean := t.unclean + u.unclean, noRun := t.noRun + u.noRun,
    wrong := mergeCounts t.wrong u.wrong, wasted := mergeCounts t.wasted u.wasted,
    recompiled := t.recompiled + u.recompiled, byEdit := mergeCounts t.byEdit u.byEdit,
    smallest := match t.smallest, u.smallest with
      | none, s => s
      | s, none => s
      | some (b, b', e), some (c, c', f) =>
        if c.size < b.size || (c.size == b.size && c'.size < b'.size) then some (c, c', f)
        else some (b, b', e) }

/-- Tallies per variant, and the number of skipped pairs, for a chunk of bases. -/
def checkChunkE (bases : List Cfg) : Array Tally × ℕ := Id.run do
  let mut ts : Array Tally := variants.toArray.map fun _ => {}
  let mut skipped := 0
  for k in bases do
    if !k.legal then skipped := skipped + (edits k).length; continue
    for (k', e) in edits k do
      if !k'.legal then skipped := skipped + 1; continue
      let mut j := 0
      for v in variants do
        ts := ts.modify j (·.add k k' e (runVariant v k k' e))
        j := j + 1
  return (ts, skipped)

def chunksE (n : ℕ) : List Cfg → ℕ → List (List Cfg)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunksE n (l.drop n) fuel

def mainErasure (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  (← IO.getStdout).flush
  let tasks := (chunksE 200 bases bases.length).map fun ch => Task.spawn fun _ => checkChunkE ch
  let results := tasks.map Task.get
  let skipped := (results.map (·.2)).sum
  IO.println s!"{skipped} pairs skipped: base or edit does not compile"
  let mut j := 0
  for v in variants do
    let t := results.foldl (fun acc r => acc.merge r.1[j]!) ({} : Tally)
    IO.println s!"{v.name}: {t.unclean} unclean, {t.noRun} out of fuel, {t.recompiled} recompiles"
    IO.println s!"  wrong: {showCounts t.wrong}"
    IO.println s!"  unclean by edited class: {showCounts t.byEdit}"
    IO.println s!"  wasted: {showCounts t.wasted}"
    match t.smallest with
    | some (k, k', e) => IO.println s!"  smallest: base {cfgStr k}\n    edit {repr e} → {cfgStr k'}"
    | none => pure ()
    j := j + 1

end erasure

section implicit
open Zinc.ImplicitScope

structure ITally where
  unclean : ℕ := 0
  noRun : ℕ := 0
  wrong : List (Cls × ℕ) := allCls.map (·, 0)
  wasted : List (Cls × ℕ) := allCls.map (·, 0)
  recompiled : List (Cls × ℕ) := allCls.map (·, 0)
  byEdit : List (Cls × ℕ) := allCls.map (·, 0)
  /-- Runs recompiling a client the baseline does not, and the reverse. -/
  moreClients : ℕ := 0
  fewerClients : ℕ := 0
  smallest : Option (Cfg × Cfg × Cls) := none
  smallestMore : Option (Cfg × Cfg × Cls) := none
  deriving Inhabited

def ibump (l : List (Cls × ℕ)) (cs : List Cls) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, if cs.contains c then n + 1 else n)

def smaller (k k' : Cfg) (e : Cls) : Option (Cfg × Cfg × Cls) → Option (Cfg × Cfg × Cls)
  | none => some (k, k', e)
  | some (b, b', e') =>
    if k.size < b.size || (k.size == b.size && k'.size < b'.size) then some (k, k', e)
    else some (b, b', e')

def ITally.add (t : ITally) (k k' : Cfg) (e : Cls) (base : Option Report) :
    Option Report → ITally
  | none => { t with noRun := t.noRun + 1 }
  | some r =>
    let bad := !r.wrong.isEmpty
    let cl := r.recompiled.filter isClient
    let bcl := ((base.map (·.recompiled)).getD []).filter isClient
    let more := cl.any (!bcl.contains ·)
    let fewer := bcl.any (!cl.contains ·)
    { t with
      unclean := t.unclean + (if bad then 1 else 0)
      wrong := ibump t.wrong r.wrong
      wasted := ibump t.wasted r.wasted
      recompiled := ibump t.recompiled r.recompiled
      byEdit := if bad then ibump t.byEdit [e] else t.byEdit
      moreClients := t.moreClients + (if more then 1 else 0)
      fewerClients := t.fewerClients + (if fewer then 1 else 0)
      smallest := if bad then smaller k k' e t.smallest else t.smallest
      smallestMore := if more then smaller k k' e t.smallestMore else t.smallestMore }

def icfgStr (k : Cfg) : String :=
  (toString (repr k)).replace "\n" " " |>.replace "Zinc.ImplicitScope." ""

def ishowCounts (l : List (Cls × ℕ)) : String :=
  ", ".intercalate ((l.filter (·.2 != 0)).map fun (c, n) =>
    s!"{(toString (repr c)).replace "Zinc.ImplicitScope.Cls." ""} {n}")

def mainImplicit : IO Unit := do
  IO.println s!"{cfgs.length} bases, {(cfgs.flatMap edits).length} edits"
  let mut ts : Array ITally := variants.toArray.map fun _ => {}
  for k in cfgs do
    for (k', e) in edits k do
      let rs := variants.map fun v => runVariant v k k' e
      let base := rs.head?.join
      let mut j := 0
      for r in rs do
        ts := ts.modify j (·.add k k' e base r)
        j := j + 1
  let mut j := 0
  for v in variants do
    let t := ts[j]!
    IO.println s!"{v.name}: {t.unclean} unclean, {t.noRun} out of fuel"
    IO.println s!"  wrong: {ishowCounts t.wrong}"
    IO.println s!"  unclean by edited class: {ishowCounts t.byEdit}"
    IO.println s!"  recompiled: {ishowCounts t.recompiled}"
    IO.println s!"  wasted: {ishowCounts t.wasted}"
    IO.println s!"  vs baseline: {t.moreClients} runs recompile a client it does not, {t.fewerClients} miss one it recompiles"
    match t.smallest with
    | some (k, k', e) => IO.println s!"  smallest unclean: base {icfgStr k}\n    edit {(toString (repr e)).replace "Zinc.ImplicitScope.Cls." ""} → {icfgStr k'}"
    | none => pure ()
    match t.smallestMore with
    | some (k, k', e) => IO.println s!"  smallest extra client: base {icfgStr k}\n    edit {(toString (repr e)).replace "Zinc.ImplicitScope.Cls." ""} → {icfgStr k'}"
    | none => pure ()
    j := j + 1

/-- Single loop with in-project rules vs one loop per project: do they agree run for run? -/
def mainComposed : IO Unit := do
  let cases : List (String × Ext × Layout × ℕ) :=
    [("develop, lib → app", develop, twoP, 2), ("develop, lib → mid → app", develop, threeP, 3),
     ("fix (stored), lib → app", stored, twoP, 2), ("fix (stored), lib → mid → app", stored, threeP, 3),
     ("fix (stored) without the fold, lib → mid → app", { stored with fold := false }, threeP, 3),
     ("develop, one project", develop, oneP, 1)]
  for (name, x, lay, nP) in cases do
    let mut runs := 0
    let mut wrongDiff := 0
    let mut clientDiff := 0
    let mut uncleanSingle := 0
    let mut uncleanComposed := 0
    let mut first : Option String := none
    for k in cfgs do
      for (k', e) in edits k do
        runs := runs + 1
        let a := report x (.proj lay) k.src k'.src {e}
        let b := reportComposed x lay nP k.src k'.src {e}
        let wa := (a.map (·.wrong)).getD []
        let wb := (b.map (·.wrong)).getD []
        if !wa.isEmpty then uncleanSingle := uncleanSingle + 1
        if !wb.isEmpty then uncleanComposed := uncleanComposed + 1
        let ca := ((a.map (·.recompiled)).getD []).filter isClient
        let cb := ((b.map (·.recompiled)).getD []).filter isClient
        if wa != wb then
          wrongDiff := wrongDiff + 1
          if first.isNone then
            first := some s!"base {icfgStr k}\n    edit {repr e} → {icfgStr k'}\n    single {repr wa}, composed {repr wb}"
        if ca != cb then clientDiff := clientDiff + 1
    IO.println s!"{name}: {runs} runs, unclean single {uncleanSingle} / composed {uncleanComposed}, wrong sets differ {wrongDiff}, client recompiles differ {clientDiff}"
    match first with
    | some str => IO.println s!"  first difference: {str}"
    | none => pure ()

end implicit

section pingpong

namespace PP
open Zinc.PingPong (U compiler zincPolicy)
open IncComp.Compiler (State Policy)

abbrev PState := State U Zinc.PingPong.Out Zinc.PingPong.K

def allU : List U := [.A, .B, .C]
def S : Finset U := {.A, .B, .C}

def tbl (t : ℕ × ℕ × ℕ) : Fin 3 → ℕ := fun i => [t.1, t.2.1, t.2.2].getD i.val 0

/-- A program: what each class reads, the edited class, its new table (the others copy). -/
structure Case where
  rd : U → U
  e : U
  t : ℕ × ℕ × ℕ

def Case.src (c : Case) : U → Zinc.PingPong.Src :=
  fun u => ⟨c.rd u, if u = c.e then tbl c.t else fun i => i.val⟩

/-- Rounds until the loop stops, or `none` within the fuel. -/
def rounds (P : Policy U Zinc.PingPong.Out Zinc.PingPong.K) (src : U → Zinc.PingPong.Src) :
    ℕ → ℕ → Finset U → PState → Option ℕ
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := compiler.round src R s
    let I := compiler.invalidated S R s s'
    if I ⊆ R then some (n + 1) else rounds P src fuel (n + 1) (P n R s s' I) s'

/-- Zinc with `transitiveStep k`: its own next round before `k`, brute force from `k` on. -/
def zincWithStep (k : ℕ) : Policy U Zinc.PingPong.Out Zinc.PingPong.K := fun n R s s' I =>
  zincPolicy n R s s' I ∪ (if k ≤ n then Policy.transitiveStep S k n R s s' I else ∅)

/-- The length of the cycle of reads through `e`, or 0. -/
def cycleLen (rd : U → U) (e : U) : ℕ :=
  if rd e = e then 1 else if rd (rd e) = e then 2 else if rd (rd (rd e)) = e then 3 else 0

def uStr : U → String | .A => "A" | .B => "B" | .C => "C"

structure PTally where
  runs : ℕ := 0
  early : ℕ := 0
  late : ℕ := 0
  never : ℕ := 0
  neverByCycle : List ℕ := [0, 0, 0, 0]
  first : Option String := none
  deriving Inhabited

def mainPingPong : IO Unit := do
  let us := allU
  let rds : List (U → U) := do
    let a ← us; let b ← us; let c ← us
    pure fun u => match u with | .A => a | .B => b | .C => c
  let ts : List (ℕ × ℕ × ℕ) := do
    let a ← [0, 1, 2]; let b ← [0, 1, 2]; let c ← [0, 1, 2]; pure (a, b, c)
  let vs : List (U → ℕ) := do
    let a ← [0, 1, 2]; let b ← [0, 1, 2]; let c ← [0, 1, 2]
    pure fun u => match u with | .A => a | .B => b | .C => c
  let pols : List (String × Policy U Zinc.PingPong.Out Zinc.PingPong.K) :=
    [("model's plain loop (invalidated classes only)", Policy.plain),
     ("Zinc's next round (invalidated + API-changed), no transitiveStep", zincPolicy),
     ("Zinc's next round with transitiveStep 3", zincWithStep 3)]
  let mut tallies : Array PTally := pols.toArray.map fun _ => {}
  for rd in rds do
    for e in us do
      for t in ts do
        if t == (0, 1, 2) then continue
        let c : Case := ⟨rd, e, t⟩
        for v in vs do
          -- a per-unit fixed point of the old sources (every class copies)
          if !(us.all fun u => v u == v (rd u)) then continue
          let s₀ : PState := { out := v, U := fun u => {(rd u, Zinc.PingPong.K.val)} }
          let mut j := 0
          for (_, P) in pols do
            let r := rounds P c.src 40 0 {e} s₀
            let tl := tallies[j]!
            let tl := { tl with runs := tl.runs + 1 }
            let tl := match r with
              | some n => if n ≤ 2 then { tl with early := tl.early + 1 } else { tl with late := tl.late + 1 }
              | none =>
                let k := cycleLen rd e
                { tl with never := tl.never + 1,
                          neverByCycle := tl.neverByCycle.modify k (· + 1),
                          first := tl.first.orElse fun _ => some
                            s!"reads A→{uStr (rd .A)} B→{uStr (rd .B)} C→{uStr (rd .C)}; edit {uStr e}'s table to {repr t}; start {repr (us.map v)}" }
            tallies := tallies.set! j tl
            j := j + 1
  let mut j := 0
  for (name, _) in pols do
    let tl := tallies[j]!
    IO.println s!"{name}: {tl.runs} runs; stop by round 2: {tl.early}; stop later: {tl.late}; never stop (40 rounds): {tl.never}"
    IO.println s!"  never-stopping runs by the length of the read cycle through the edited class (none, 1, 2, 3): {repr tl.neverByCycle}"
    match tl.first with
    | some str => IO.println s!"  first: {str}"
    | none => pure ()
    j := j + 1

end PP

end pingpong

open Zinc.Flat Zinc.Flat.Shared in
/-- `Flat` against the shared semantics, over `FlatRules.cfgs`, in parallel chunks; refchecks per
dialect, and the commonest disagreements under the given one. -/
def mainFlatShared (args : List String) : IO Unit := do
  let dl : Scala.Dialect := match args.head? with
    | some "2.12" => .s212 | some "3" => .s3 | _ => .s213
  let sp := cfgs
  let chunk := 5000
  let parts := (List.range ((sp.length + chunk - 1) / chunk)).map fun i => (sp.drop (i * chunk)).take chunk
  let tasks := parts.map fun part => Task.spawn fun _ =>
    part.foldl (init := (List.replicate 2 (0, 0, 0, 0))) fun acc k =>
      let (l, sl, e) := check k dl
      let i := if k.oM == .var then 1 else 0
      acc.modify i fun (n, a, b, c) =>
        (n + 1, a + (if l then 1 else 0), b + (if sl then 1 else 0), c + (if e then 1 else 0))
  let rs := tasks.map Task.get
  let sum := rs.foldl (fun a r => (a.zip r).map fun ((n, x, y, z), (n', x', y', z')) =>
    (n + n', x + x', y + y', z + z')) (List.replicate 2 (0, 0, 0, 0))
  IO.println s!"refchecks against {repr dl}"
  for (nm, (n, l, sl, e)) in ["without a var", "the trait declares a var"].zip sum do
    IO.println s!"{nm}: {n} programs; linearization agrees {l}, selections {sl}, refchecks {e}"
  -- the commonest disagreement patterns, without a var
  let nv := sp.filter (·.oM != .var)
  let verdicts := (parts.map fun part => Task.spawn fun _ =>
    (part.filter fun k => k.oM != .var && verdictAgrees k.src dl).length).map Task.get
  IO.println s!"without a var: every class compiles under both, or fails under both, in {verdicts.foldl (· + ·) 0} of {nv.length}"
  let bad := (nv.filter fun k => !verdictAgrees k.src dl).map fun k => (errPattern k dl, k)
  let mut counts : List (String × Nat × Cfg) := []
  for (p, k) in bad do
    match counts.findIdx? (·.1 == p) with
    | some i => counts := counts.modify i fun (p, n, k) => (p, n + 1, k)
    | none => counts := counts ++ [(p, 1, k)]
  let top := (counts.toArray.qsort (fun a b => a.2.1 > b.2.1)).toList.take 12
  for (p, n, k) in top do
    IO.println s!"{n}× {p}"
    IO.println s!"    e.g. {repr k}"

def main (args : List String) : IO Unit :=
  match args with
  | "erasure" :: rest => mainErasure rest
  | "implicit" :: _ => mainImplicit
  | "composed" :: _ => mainComposed
  | "pingpong" :: _ => PP.mainPingPong
  | "flatshared" :: rest => mainFlatShared rest
  | "v" :: _ => mainV
  | "precision" :: "why" :: rest => mainPrecisionWhy rest
  | "precision" :: rest => mainPrecision rest
  | _ => mainRules args
