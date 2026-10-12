import Jvm.Catalogue

/-! Formatting catalogue cases for the literate pages: one line per case. -/

namespace Literate
open Jvm Jvm.Catalogue

/-- The last component of a constructor's name. -/
def short {α} [Repr α] (a : α) : String :=
  ((reprStr a).splitOn ".").getLast!

/-- An outcome: the error, or the classes whose code ran. -/
def fmt : Except LinkError (List C) → String
  | .ok [] => "loads"
  | .ok cs => "runs " ++ ", ".intercalate (cs.map short)
  | .error e => short e

/-- A case: its outcome before and after the edit, and the problem MiMa 1.2.1 reports. -/
def caseRow (k : Case) : String :=
  s!"{k.name}: {fmt k.before} → {fmt k.after}" ++
    match k.mima with
    | some p => s!" ({p})"
    | none => " (MiMa: nothing)"

/-- A case without the MiMa column. -/
def caseRow' (k : Case) : String :=
  s!"{k.name}: {fmt k.before} → {fmt k.after}"

end Literate
