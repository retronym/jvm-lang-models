import MiMa.Fixed
/-!
# The reversed edits, judged with a library body (Track J4)

MiMa reports `ReversedMissingMethodProblem` for 17 edits of the edit space (`MiMa.Edits`) that break
no client of `spaceB`: each adds an abstract method to a class or interface, and only a library
method's own call can reach it. Here each such edit comes with the template method that makes it
observable: the class or interface that gains the abstract `m` declares `run()V`, with an empty body
in `v0` and `this.m()` in `v1` (`invokeinterface` for an interface). A client is a class `X`
below it (superclass none, `A` or `B`; interfaces any subset of `I`, `J`), declaring `m()V` or
`m()I` with any access, or no `m`, and calling `run` on an `X`.

Every one of the 17 breaks such a client (kernel `decide` below; on HotSpot, `lake exe bincompat
reversed` and `packages/jvm/probes/probe.sh`): `run` throws `AbstractMethodError` when `X` does not
implement the new method. So MiMa's reports are true positives once the library calls its own
abstract method, which is what `ReversedMissingMethodProblem` warns about.
-/

namespace MiMa

open Jvm Jvm.Catalogue Jvm.Clients

/-- The abstract method an edit adds, if any: its class and descriptor. -/
def addedAbstract (o n : Lib) : Option (C × D) :=
  n.findSome? fun (c, cf) => cf.methods.findSome? fun (mn, d, i) =>
    if i.isAbstract && !(((get o c).map (·.methods)).getD []).any (fun m => m.1 = mn ∧ m.2.1 = d)
    then some (c, d) else none

/-- `l` with `run()V`, of body `body`, added to `c`. -/
def withRun (l : Lib) (c : C) (body : List (Site C N D)) : Lib :=
  l.map fun (x, cf) => if x = c then (x, { cf with methods := cf.methods ++ [(.run, .v, { body })] }) else (x, cf)

/-- An edit adding an abstract `m` to `c`, with `c.run()` calling it in `v1`. -/
def Edit.withHook (e : Edit) : Option (Case × C × Bool) := do
  let (c, d) ← addedAbstract e.v0 e.v1
  let itf := isIface e.v1 c
  let call : Site C N D := if itf then .invokeinterfaceThis c .m d else .invokevirtualThis c .m d
  pure ({ name := e.name ++ "+run", mima := some "ReversedMissingMethodProblem",
          v0 := withRun e.v0 c [], v1 := withRun e.v1 c [call], prog := {} }, c, itf)

def xClassesR : List (Classfile C N D) := do
  let s ← [none, some C.A, some C.B]
  let is ← [[], [C.I], [C.J], [C.I, C.J]]
  let ms ← [] :: ([D.v, D.i].flatMap fun d => accesses.map fun a => [(N.m, d, { access := a })])
  pure { header := { super := s, ifaces := is }, methods := ms }

/-- The clients that call `run` through `c`. -/
def hookClients (c : C) (itf : Bool) : List Client :=
  xClassesR.map fun x =>
    ([(.X, x)], { loads := [.X], sites := [if itf then .invokeinterface c .run .v .X else .invokevirtual c .run .v .X] })

/-- The edits MiMa reports as `ReversedMissingMethodProblem` and nothing else, which break no client
of `spaceB` (`lake exe bincompat verdicts`). -/
def reversedNames : List String :=
  ["b1-33", "b1-34", "b1-35", "b1-95", "b1-96", "b1-97", "b1-133", "b1-143", "b1-148",
   "b2-33", "b2-34", "b2-35", "b2-94", "b2-95", "b2-96", "b2-131", "b2-146"]

def reversedEdits : List Edit := edits.filter fun e => reversedNames.contains e.name

/-- Each reversed edit with its hook, and the first client of `hookClients` that breaks. -/
def reversedBreaking : List (Edit × Option Client) :=
  reversedEdits.map fun e => match e.withHook with
    | some (k, c, itf) => (e, breaking k (hookClients c itf))
    | none => (e, none)

/-- The 17 are exactly the edits of the space MiMa reports with `ReversedMissingMethodProblem` alone. -/
example : (edits.filter fun e => mima e.v0 e.v1 = [.reversedMissingMethod]).map (·.name) = reversedNames := by
  decide +kernel

/-- Each breaks a client once the library calls the new method on `this`, and the corrected rules
report each (they include MiMa's). -/
example : reversedBreaking.all (·.2.isSome) = true ∧ reversedEdits.all (fun e => fixedReports e.v0 e.v1) = true := by
  decide +kernel

end MiMa
