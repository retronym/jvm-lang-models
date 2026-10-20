import Scala.Names
/-! `namesprobe OUT`: each program of `Scala.Names.namesSpace` as `OUT/src/pN/<file>.scala`, the
family of each in `OUT/index.txt` (`pN`, family, `3` if only Scala 3 compiles it, `fresh` if it is in
the empty package), and the model's classfiles per dialect in `OUT/expected-<tag>.txt`: `pN`, binary
name, and the `InnerClasses` entry's outer class and simple name (`-` for none), or `!unwritable` when
a name is too long for a file on APFS, where the probe runs. Read by `packages/scala/probes/names.py`.

A compile server keeps its symbol table between runs, so programs must not define the same class:
each program's package is prefixed with `pN`, but for those in the empty package, which
`names.py` compiles each with a compiler of its own. -/

open Scala Scala.Names

def main (args : List String) : IO Unit := do
  let out := args.headD "out"
  let progs := namesSpace.zipIdx
  let mut index := ""
  let progs := progs.map fun ((fam, p), i) =>
    ((fam, if p.pkg.isEmpty then p else { p with pkg := s!"p{i}" :: p.pkg }), i)
  for ((fam, p), i) in progs do
    let dir := s!"{out}/src/p{i}"
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/{p.file}.scala" p.show
    index := index ++ s!"p{i}\t{fam}\t{if p.only3 then "3" else "-"}\t{if p.pkg.isEmpty then "fresh" else "-"}\n"
  IO.FS.writeFile s!"{out}/index.txt" index
  for (tag, dl) in [("2.12", Dialect.s212), ("2.13", .s213), ("3", .s3)] do
    let mut exp := ""
    for ((_, p), i) in progs do
      if p.only3 && dl != .s3 then continue
      let es := entries dl p
      if es.any (unwritable .apfs ·.bin) then
        exp := exp ++ s!"p{i}\t!unwritable\t-\t-\n"
        continue
      for e in es do
        let (o, s) := e.inner.getD ("-", "-")
        exp := exp ++ s!"p{i}\t{e.bin}\t{o}\t{s}\n"
    IO.FS.writeFile s!"{out}/expected-{tag}.txt" exp
  IO.println s!"{progs.length} programs"
