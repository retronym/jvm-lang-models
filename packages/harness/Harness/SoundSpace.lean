import ScalaTypes.Paths
/-! Writes Track T's first space (`ScalaTypes.Paths.space`) as Scala sources for the oracle
(`packages/scala/probes/soundness.py`), one file per program, `pNNNN.scala` by its index in the
space, and the model's verdict per setting as `model.jsonl`.

    lake exe soundspace OUT -/

open Scala.Paths

def settingName : Setting → String
  | .s212 => "2.12.21" | .s213 => "2.13.18" | .s3 => "3.9.0"
  | .s3future => "3.9.0 -source future" | .s3nulls => "3.9.0 -Yexplicit-nulls"

def caseName (i : Nat) : String :=
  let s := toString i
  "p" ++ String.ofList (List.replicate (4 - s.length) '0') ++ s

def main (args : List String) : IO Unit := do
  let some out := args.head? | throw (IO.userError "usage: soundspace OUT")
  IO.FS.createDirAll out
  let h ← IO.FS.Handle.mk (out ++ "/model.jsonl") .write
  for (p, i) in space.zipIdx do
    IO.FS.writeFile (out ++ "/" ++ caseName i ++ ".scala") p.source
    for s in Setting.all do
      h.putStrLn ("{\"case\":\"" ++ caseName i ++ "\",\"setting\":\"" ++ settingName s ++
        "\",\"model\":\"" ++ (toString (repr (verdict s p))).replace "Scala.Paths.Verdict." "" ++ "\"}")
