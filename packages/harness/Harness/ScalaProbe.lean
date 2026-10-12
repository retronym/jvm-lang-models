import Scala.Space
import ScalaTypes.Members
import Zinc.Bridges.FlatShared
/-! `scalaprobe OUT flat`: the `FlatRules` space (`Zinc.Flat.cfgs`, 216,000 configurations) as Scala,
for `packages/scala/probes/members.py --space flat`. Each configuration is lowered to the shared
syntax (`Zinc.Flat.Shared.program`) and printed; configurations that print the same program (they
differ only in client bodies, which the shared program does not carry) share one source,
`OUT/srcf/qN.scala`. `OUT/flat-index.txt` has, per program, its configurations' count and the first
one; `OUT/members-flat-<tag>.txt` the model's verdicts per dialect, as `members-<tag>.txt`. Concrete
members say which owner ran (`withOwners`). A
configuration whose trait declares a `var` is left out (`Zinc.Flat.Shared.hasVar`: `Members` has
no `var`, and the shared syntax prints it as a `def`).

`scalaprobe OUT`: write each case of `Scala.space` as Scala source, and the model's
classfiles for each dialect as `OUT/expected-2.12.txt`, `OUT/expected-2.13.txt` and
`OUT/expected-3.txt`. Sources go to `OUT/src/pN.scala`, or `OUT/src3/` for Scala 3 syntax, or, for
a case compiled in two runs, `OUT/sep/lib/pN.scala` and `OUT/sep/client/pN.scala` (`sep3` for
Scala 3 syntax). -/


open Scala

def optTag : Zinc.Flat.Opt → String
  | .none => "-" | .int => "int" | .str => "str" | .par => "par" | .dfr => "dfr" | .val => "val"
  | .var => "var" | .lzy => "lazy" | .pval => "pval"

def hTy : Zinc.Hier.Ty → String
  | .int => "Int" | .string => "String" | .param => "T" | .v => "V"

def cfgDesc (k : Zinc.Flat.Cfg) : String :=
  s!"A={optTag k.oA} B={optTag k.oB} M={optTag k.oM} C={optTag k.oC} " ++
  s!"A<:{(k.aPar.map fun t => s!"M[{hTy t}]").getD "-"} B<:A[{hTy k.bArg}]" ++
  (if k.bFinal then " finalB" else "") ++ (if k.xObj then " X<:C" else "") ++
  (if k.aTrait then " traitA" else "") ++ (if k.bUses then " bUses" else "") ++ (if k.zObs then " zObs" else "")

/-- The owner codes a concrete `Int` member returns, for the runtime check. -/
def ownerCode : String → Nat
  | "A" => 1 | "B" => 2 | "M" => 3 | "C" => 4 | _ => 0

/-- Concrete members that say which owner ran: an `Int` member returns its owner's code, a `String`
member its owner's name, and a member of the class's type parameter prints `@owner` (its value
cannot carry it: the parameter may be instantiated to `Int` or `String` along the way). -/
def withOwners (p : Program) : Program :=
  p.map fun s => { s with cls := s.cls.map fun d => { d with members := d.members.map fun m =>
    if m.abs then m else { m with rhs := some (match m.res with
      | .int => toString (ownerCode d.name)
      | .str => s!"\"{d.name}\""
      | .tp _ _ => s!"\{ print(\"@{d.name} \"); null.asInstanceOf[{(Ty.tp [d.name] 0).show}] }"
      | t => body t) } } }

def mainFlat (out : String) : IO UInt32 := do
  IO.FS.createDirAll s!"{out}/srcf"
  -- distinct programs, by their printed source
  let mut ids : Std.HashMap String Nat := {}
  let mut progs : Array (Program × String × Nat) := #[]
  let mut skipped := 0
  for k in Zinc.Flat.cfgs do
    if Zinc.Flat.Shared.hasVar k then skipped := skipped + 1; continue
    let p := withOwners (Zinc.Flat.Shared.program k.src)
    let txt := p.show "PKG"
    match ids[txt]? with
    | some i => progs := progs.modify i fun (p, d, n) => (p, d, n + 1)
    | none =>
      ids := ids.insert txt progs.size
      progs := progs.push (p, cfgDesc k, 1)
  let mut index := ""
  for ((p, d, n), i) in progs.toList.zipIdx do
    IO.FS.writeFile s!"{out}/srcf/q{i}.scala" (p.show s!"q{i}")
    index := index ++ s!"q{i}\t{n}\t{d}\n"
  IO.FS.writeFile s!"{out}/flat-index.txt" index
  for (dl, tag) in [(Dialect.s212, "2.12"), (.s213, "2.13"), (.s3, "3")] do
    let mut lines : Array String := #[]
    for ((p, _), i) in progs.toList.zipIdx do
      match Members.reported dl p with
      | .ok es =>
        for e in es do lines := lines.push s!"q{i}\terr\t{e.cls}\t{e.kind.name}"
        for (c, o) in Members.runs p do lines := lines.push s!"q{i}\trun\t{c}\t{o}"
      | .error e => IO.eprintln s!"q{i}: {e}"; return 1
    IO.FS.writeFile s!"{out}/members-flat-{tag}.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{Zinc.Flat.cfgs.length} configurations, {skipped} with a var left out, {progs.size} distinct programs"
  return 0

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  if args.drop 1 == ["flat"] then return ← mainFlat out
  for d in ["src", "src3", "sep/lib", "sep/client", "sep3/lib", "sep3/client"] do IO.FS.createDirAll s!"{out}/{d}"
  let mut index := ""
  for (c, i) in space.zipIdx do
    let pkg := s!"p{i}"
    if c.lib.isEmpty then
      IO.FS.writeFile s!"{out}/{if c.only3 then "src3" else "src"}/{pkg}.scala" (c.prog.show pkg)
    else
      let (l, r) := c.prog.partition fun s => c.lib.contains s.name
      let shw (us : Program) := s!"package {pkg}\n\n" ++ String.join (us.map (Src.show c.prog))
      let sep := if c.only3 then "sep3" else "sep"
      IO.FS.writeFile s!"{out}/{sep}/lib/{pkg}.scala" (shw l)
      IO.FS.writeFile s!"{out}/{sep}/client/{pkg}.scala" (shw r)
    index := index ++ s!"{pkg}\t{c.fam}\n"
  IO.FS.writeFile s!"{out}/index.txt" index
  for (dl, tag) in [(Dialect.s212, "2.12"), (.s213, "2.13"), (.s3, "3")] do
    let mut lines : Array String := #[]
    for (c, i) in space.zipIdx do
      if c.only3 && dl != .s3 then continue
      match c.lower dl with
      | .ok cs => for k in cs do lines := lines ++ (k.dump s!"p{i}").toArray
      | .error e => IO.eprintln s!"p{i}: {e}"; return 1
    IO.FS.writeFile s!"{out}/expected-{tag}.txt" ("\n".intercalate lines.toList ++ "\n")
  -- membership: sources in `srcm/`, the model's verdicts per dialect in `members-<tag>.txt`
  IO.FS.createDirAll s!"{out}/srcm"
  let mut mindex := ""
  for ((desc, p), i) in Members.membersSpace.zipIdx do
    IO.FS.writeFile s!"{out}/srcm/q{i}.scala" (p.show s!"q{i}")
    mindex := mindex ++ s!"q{i}\t{desc}\n"
  IO.FS.writeFile s!"{out}/members-index.txt" mindex
  for (dl, tag) in [(Dialect.s212, "2.12"), (.s213, "2.13"), (.s3, "3")] do
    let mut lines : Array String := #[]
    for ((_, p), i) in Members.membersSpace.zipIdx do
      match Members.reported dl p with
      | .ok es =>
        for e in es do lines := lines.push s!"q{i}\terr\t{e.cls}\t{e.kind.name}"
        for (c, o) in Members.runs p do lines := lines.push s!"q{i}\trun\t{c}\t{o}"
      | .error e => IO.eprintln s!"q{i}: {e}"; return 1
    IO.FS.writeFile s!"{out}/members-{tag}.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{space.length} programs, {Members.membersSpace.length} membership programs"
  return 0
