import MiMa
import Links
import Jvm.Dump
import Scala.Catalogue
import Scala.Space
/-! `lake exe bincompat`, for `packages/mima/probes`.

* `finalBehind`: `MiMa.finalBehindEdits` (Track J6's `methodBecomesFinalBehind` over the chain
  space): how many break their client, how many of those `Fixed` misses, and how many of those have a
  library that still loads by itself;
* `edits`: the edit space (`packages/mima/MiMa/Edits.lean`) as `Jvm` case JSON lines (no client), for
  `packages/jvm/probes/probe.sh` to render with `OUT=dir`;
* `mima`: the model's MiMa problems per edit and per `Jvm` catalogue case, as JSON lines;
* `gaps`: the witnesses of `packages/mima/MiMa/Keys.lean`, as `Jvm` case JSON lines;
* `scala OUT`: each `packages/scala/Scala/Catalogue.lean` case's library sources as `OUT/<case>/v0.scala` and
  `v1.scala` (package `p`), its client as `client.scala`, its sites and the model's outcomes as
  `case.json` (in `packages/jvm/probes`' format, names unqualified, for `packages/scala/probes/run.py`),
  and per case a TSV line: name, expected MiMa problem, the model's
  outcome before, after and fresh;
* `reversed`: the 17 `ReversedMissingMethodProblem` edits with a hook (`MiMa.Reversed`), each with
  every well-typed client of its hook space, as `Jvm` case JSON lines for `packages/jvm/probes/probe.sh`;
* `verdicts`: per edit, the model's MiMa problems and whether some client of `spaceB` breaks or
  changes, as TSV. -/

open IncComp

open MiMa Links Jvm.Catalogue Jvm.Clients

def jstr (s : String) : String := "\"" ++ s ++ "\""

/-- A `Jvm.Site` over names as strings, in `packages/jvm/probes`' JSON (names unqualified). -/
def siteJsonS : Jvm.Site String String String → String
  | .invokestatic c n d => s!"\{\"op\":\"invokestatic\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d}}"
  | .invokestaticIface c n d => s!"\{\"op\":\"invokestaticIface\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d}}"
  | .invokevirtual c n d r => s!"\{\"op\":\"invokevirtual\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d},\"recv\":{jstr r}}"
  | .invokeinterface c n d r => s!"\{\"op\":\"invokeinterface\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d},\"recv\":{jstr r}}"
  | .getstatic c n d => s!"\{\"op\":\"getstatic\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d}}"
  | .new c => s!"\{\"op\":\"new\",\"owner\":{jstr c}}"
  | .construct c n d => s!"\{\"op\":\"construct\",\"owner\":{jstr c},\"name\":{jstr n},\"desc\":{jstr d}}"
  | _ => "{\"op\":\"unsupported\"}"

def outcomeJsonS : Except String (Except Jvm.LinkError (List String)) → String
  | .ok (.ok l) => "{\"ok\":[" ++ ",".intercalate (l.map jstr) ++ "]}"
  | .ok (.error e) => "{\"error\":" ++ jstr (Jvm.Dump.errName e) ++ "}"
  | .error m => "{\"lowering\":" ++ jstr m ++ "}"

def problemsJson (name : String) (ps : List Problem) : String :=
  "{\"name\":" ++ jstr name ++ ",\"problems\":[" ++ ",".intercalate (ps.map (jstr ∘ Problem.name)) ++ "]}"

def main (args : List String) : IO Unit := do
  if args.contains "gaps" then
    for (n, x) in [("finalField", finalField), ("shadowStatic", shadowStatic), ("shadowField", shadowField),
        ("overridePrivate", overridePrivate), ("ifaceField", ifaceField),
        ("defaultConflict", defaultConflict), ("protectedRemoved", protectedRemoved)] do
      IO.println (Jvm.Dump.caseJson { name := n, mima := none, v0 := x.o, v1 := x.n, client := x.client, prog := x.prog })
  else if args.contains "scala" then
    let out := args.getLast!
    for k in Scala.Catalogue.all do
      IO.FS.createDirAll s!"{out}/{k.name}"
      IO.FS.writeFile s!"{out}/{k.name}/v0.scala" (k.v0.show "p")
      IO.FS.writeFile s!"{out}/{k.name}/v1.scala" (k.v1.show "p")
      IO.FS.writeFile s!"{out}/{k.name}/client.scala" (k.client.show "p")
      IO.FS.writeFile s!"{out}/{k.name}/case.json" <|
        "{\"name\":" ++ jstr k.name ++ ",\"mima\":null,\"v0\":[],\"v1\":[],\"client\":[]" ++
        ",\"loads\":[" ++ ",".intercalate (k.loads.map jstr) ++ "],\"sites\":[" ++
        ",".intercalate (k.sites.map siteJsonS) ++ "],\"before\":" ++ outcomeJsonS k.before ++
        ",\"after\":" ++ outcomeJsonS k.after ++ "}"
      IO.println s!"{k.name}\t{k.mima.getD ""}\t{repr k.before}\t{repr k.after}\t{repr k.fresh}"
  else if args.contains "finalBehind" then
    let ks := finalBehindEdits
    let br := ks.filter fun k => links k.w0 k.prog && !links k.w1 k.prog
    let silent := br.filter fun k => !fixedReports k.v0 k.v1
    IO.println s!"{ks.length} edits, {br.length} break their client, {silent.length} of them unreported by Fixed, {(ks.filter finalBehindMissed).length} of those with a library that still loads by itself"
  else if args.contains "edits" then
    for e in edits do IO.println (Jvm.Dump.caseJson e.case)
  else if args.contains "mima" then
    for e in edits do IO.println (problemsJson e.name (mima e.v0 e.v1))
    for k in all ++ j3 ++ j5 ++ j7 ++ j8 ++ jObject do IO.println (problemsJson k.name (mima k.v0 k.v1))
  else if args.contains "unreported" then
    for b in [1, 2] do
      for c in [C.A, C.B, C.I, C.J] do
        IO.println s!"{b} {repr c} {nVariants b c} {unreported b c}"
  else if args.contains "witness" then
    for e in edits do
      if args.contains e.name then
        match breaking e.case spaceB with
        | some cl => IO.println s!"{e.name}\t{Jvm.Dump.caseJson (e.case.withClient cl)}"
        | none => IO.println s!"{e.name}\tnone"
  else if args.contains "reversed" then
    for e in reversedEdits do
      if let some (k, c, itf) := e.withHook then
        for (cl, i) in (hookClients c itf).zipIdx do
          let k' := k.withClient cl
          if wellTyped k'.w0 cl.2 then IO.println (Jvm.Dump.caseJson { k' with name := s!"{k.name}/{i}" })
  else if args.contains "verdicts" then
    for e in edits do
      let k := e.case
      let br := breaking k spaceB
      let ch := changing k spaceB
      IO.println s!"{e.name}\t{",".intercalate ((mima e.v0 e.v1).map Problem.name)}\t{br.isSome}\t{ch.isSome}\t{",".intercalate ((extra e.v0 e.v1).map Extra.name)}"
