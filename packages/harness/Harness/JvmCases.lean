import Jvm.Dump
import Jvm.Clients
import MiMa.Edits
/-! `lake exe jvmcases`: the catalogue (`packages/jvm/Jvm/Catalogue.lean`) as JSON lines for `packages/jvm/probes`.

`lake exe jvmcases space`: every catalogue edit with every well-typed client of `packages/jvm/Jvm/Clients.lean`'s
space (`space3` for the Track J3 cases, `space5` for Track J5), named `<case>/<n>`, so the probe checks the model's outcome for each client, not only the
catalogue's own.

`lake exe jvmcases chain`: the Track J6 space of overriding chains (`Jvm.Clients.chainSpace`), each a case with
`v1 = v0`.

`lake exe jvmcases count`: the catalogue's size and each client space's, as tab-separated lines (catalogue
group or space, clients, programs) for `scripts/model_stats.py`. A space's programs are the well-typed
(case, client) pairs that `space` dumps; `chainSpace`'s are its cases; MiMa's `spaceB` is counted in clients.

`lake exe jvmcases verdicts`: per edit, MiMa's problem, the Track J2 verdicts and the number of clients in
the space that break or change, as a markdown table. -/


open Jvm.Catalogue Jvm.Clients

/-- The well-typed (case, client) pairs of `cases` over `space`: the programs the probe runs. -/
def programs (cases : List Case) (space : List Client) : Nat :=
  cases.foldl (fun n k => n + (space.filter fun cl => wellTyped (k.withClient cl).w0 cl.2).length) 0

def main (args : List String) : IO Unit := do
  if args.contains "count" then
    IO.println s!"catalogue\tJ1–J2\t{all.length}"
    IO.println s!"catalogue\tJ3\t{j3.length}"
    IO.println s!"catalogue\tJ5\t{j5.length}"
    IO.println s!"catalogue\tJ4\t{j4.length}"
    IO.println s!"space\tspace\t{space.length}\t{programs all space}"
    IO.println s!"space\tspace3\t{space3.length}\t{programs j3 space3}"
    IO.println s!"space\tspace5\t{space5.length}\t{programs j5 space5}"
    IO.println s!"space\tchainSpace\t{chainSpace.length}\t{chainSpace.length}"
    IO.println s!"space\tMiMa.spaceB\t{MiMa.spaceB.length}\t"
    return
  if args.contains "chain" then
    for k in chainSpace do
      IO.println (Jvm.Dump.caseJson k)
    return
  if args.contains "j3" then
    for k in j3 do
      IO.println s!"{k.name}\t{repr k.before}\t{repr k.after}"
    return
  let cases := if args.contains "space" || args.contains "verdicts" then
      all.map (·, space) ++ j3.map (·, space3) ++ j5.map (·, space5)
    else (all ++ j3 ++ j5 ++ j4).map (·, space)
  for (k, space) in cases do
    if args.contains "verdicts" then
      let ok := space.filter fun cl => let k' := k.withClient cl; wellTyped k'.w0 cl.2 && links k'.w0 cl.2
      let br := ok.filter fun cl => !links (k.withClient cl).w1 cl.2
      let ch := ok.filter fun cl => let k' := k.withClient cl; links k'.w1 cl.2 && k'.before != k'.after
      IO.println s!"| `{k.name}` | {k.mima.getD "—"} | {breaksSomeClient k space} | {changesSomeClient k space} | {br.length}/{ok.length} | {ch.length}/{ok.length} |"
    else if args.contains "space" then
      for (cl, i) in space.zipIdx do
        let k' := k.withClient cl
        if wellTyped k'.w0 cl.2 then
          IO.println (Jvm.Dump.caseJson { k' with name := s!"{k.name}/{i}" })
    else
      IO.println (Jvm.Dump.caseJson k)
