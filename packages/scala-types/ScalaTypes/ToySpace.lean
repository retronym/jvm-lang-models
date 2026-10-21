import ScalaTypes.ToyKernel
/-!
# A space of scenarios for the kernel

`results.txt` ran seven scenarios written by hand after the PR's tests. The kernel in Lean runs in
milliseconds, so the harness can run over a *space*: every program assembled from a menu of
declarations, in every order, with every completion and whole-unit request, under each policy.
What diverges under the policy after scala/scala#11328 is a prediction of a flaky presentation
compiler test not yet written; what diverges under the proposal is a counterexample to it.
-/

namespace ScalaTypes.ToySpace

open ScalaTypes.ToyNamer ScalaTypes.ToyKernel

/-- The menu: a case class with and without a companion of its own, an implicit class, consumers
through paths, a second case class reading the first, a deprecated member with and without a
`nowarn` consumer. -/
def menu : List Decl := [
  { isCase := true, name := "L", params := [("a", "Int")], stats := [m "self" "L"] },
  { obj := true, name := "L", stats := [m "mk" "L"] },
  { isImplicit := true, name := "RichInt", params := [("i", "Int")], stats := [m "twice" "Int"] },
  { obj := true, name := "Use", stats := [m "l" "L", inf "f" ["l", "self"], m "three" "Int", inf "g" ["three", "twice"]] },
  { isCase := true, name := "M", params := [("b", "Int")], stats := [m "l" "L", inf "h" ["l", "self"], inf "k" ["l", "a"]] },
  { name := "Old", stats := [.member { name := "m", declared := some "Int", deprecated := true }] },
  { obj := true, nowarn := true, name := "Later", stats := [m "o" "Old", inf "bar" ["o", "m"]] },
  { obj := true, name := "Use2", stats := [m "o" "Old", inf "foo" ["o", "m"], m "l" "L", inf "f2" ["l", "self"]] }]

/-- The programs: `Int` and two or three declarations of the menu, in every order. -/
def programs : List Program :=
  ((selections 2 menu) ++ (selections 3 menu)).map (intD :: ·)
  where selections {α : Type} [BEq α] : Nat → List α → List (List α)
    | 0, _ => [[]]
    | n + 1, xs => xs.flatMap fun x => (selections n (xs.filter (· != x))).map (x :: ·)

/-- The requests on a program: a completion at each inferred member, and the whole unit. -/
def requests (p : Program) : List Ask :=
  (p.flatMap fun d => d.members.filterMap fun mem => if mem.path.isEmpty then none else some (Ask.completion "A" d.name mem.name))
    ++ [.loadedTyped "A"]

def scenariosOf (p : Program) : List Scenario :=
  (requests p).map fun a => { name := String.intercalate "," (p.map (·.name)) ++ " / " ++ (match a with | .completion _ d mm => d ++ "." ++ mm | .loadedTyped _ => "unit"), units := [("A", p)], event := .request a }

def space : List Scenario := programs.flatMap scenariosOf

/-- The scenarios that diverge under `policy`, with their divergent safepoints and what the first
divergent answer is against the reference. -/
def divergences (policy : Policy) : List (String × Nat × List Nat) :=
  space.filterMap fun sc =>
    let d := divergent policy sc
    if d.isEmpty then none else some (sc.name, safepoints policy sc, d)

def firstDiff (policy : Policy) (sc : Scenario) : Option (Nat × List Answer × List Answer) :=
  match divergent policy sc with
  | [] => none
  | k :: _ => some (k, reference policy sc, atSafepoint policy sc k)

/-! ## What the space says

Evaluated (`#eval`, compiled): 1,372 scenarios over 392 programs. Under the policy before the PR
755 diverge; after it 369, of which 312 are whole-unit requests (the I1/I2 family) and 57 are
completions; under the proposal 57, the same 57 completions. Every one of those 57 has the case
class `L` declared *after* the member whose completion is asked, and diverges at exactly the
safepoints before `L`'s synthesis burst: a targeted check types the unit up to its target and never
reaches `L`, so the completion lists `L` as the namer left it, without the typer's `equals`,
`hashCode` and `toString`; the reference, after the background, has them. That is the targeting gap
of track-i.md §6, not a synthetics policy, and no policy on the burst closes it.

The space also found three things the Java toy had wrong before the Lean kernel was held to it
(§9 of the note): the implicit factory and `copy` are the namer's synthetics in scalac
(`enterClassDef`, `addCopyMethod`), not the typer's, and a replaced factory's tree is never found
by `addSynthetics`, which walks the scope. -/

/-- The consumer-first shape: `Use` before the case class `L`, completion at `Use.f : L`. -/
def consumerFirst : Scenario :=
  { name := "Int,Use,L / Use.f",
    units := [("A", [intD,
      { obj := true, name := "Use", stats := [m "l" "L", inf "f" ["l", "self"], m "three" "Int", inf "g" ["three", "twice"]] },
      { isCase := true, name := "L", params := [("a", "Int")], stats := [m "self" "L"] }])],
    event := .request (.completion "A" "Use" "f") }

/-- **The targeting gap**, observed: `divergent .proposed consumerFirst` is `[0, …, 11]`, the twelve
safepoints before `L`'s burst, of twenty (`consumerFirst_safepoints`). Stated as a theorem it is
not accepted by `decide +kernel`, which gets stuck on this scenario where it reduces the seven of
`ToyKernel.results_before_after_proposed`; the compiled evaluator runs it. Where the two differ is
an open item (track-i.md §10). -/
def consumerFirst_divergent : List Nat := divergent .proposed consumerFirst

end ScalaTypes.ToySpace
