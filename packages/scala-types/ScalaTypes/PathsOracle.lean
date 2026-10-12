import ScalaTypes.Paths
import ScalaTypes.PathsData
/-!
# Track T: the model of the checks against the compilers and the oracle

The oracle's ledger over `Scala.Paths.space` (`ScalaTypes.PathsData`, written by
`packages/scala/probes/soundness_lean.py`): for each of the five compiler settings, each program's
verdict and, where accepted, what happened when it ran on HotSpot. The theorems are decided by the
kernel over the space:

* `calibrated`: the model's verdict (`Scala.Paths.verdict`, accepted or the first error by kind) is
  the compiler's, for every program and setting;
* `accepted_sound_except`: an accepted program throws a `ClassCastException` exactly when it is in
  the named class `Unsound`, and a rejected one was not run;
* `nulls_no_cce`: under `-Yexplicit-nulls` no program of the space throws one.

`Unsound s p`: `s` accepts `p`, its path is `null` at run time (a `val` or a field initialised to
`null`, or a parameter passed `null`), and its types claim the `Int` it pushes into `L` is a
`String` at a position erasure checks: `down` returns `String`, or `L` erases to `String` as `up`'s or
`down`'s view sees it. An intersection's `L` erases as dotc erases `Int & String`, to `Int`.
-/

open Query

namespace Scala.Paths

def Verdict.code : Verdict → Nat
  | .accept => 0 | .wellFormed => 1 | .nullPath => 2 | .instantiate => 3 | .mismatch => 4
  | .notPath => 5 | .override => 6

def compiled : Setting → List Nat
  | .s212 => Data.compiled_s212 | .s213 => Data.compiled_s213 | .s3 => Data.compiled_s3
  | .s3future => Data.compiled_s3future | .s3nulls => Data.compiled_s3nulls

/-- The run: 0 not run, 1 ok, 2 `ClassCastException`, 3 expected, 4 other. -/
def ran : Setting → List Nat
  | .s212 => Data.ran_s212 | .s213 => Data.ran_s213 | .s3 => Data.ran_s3
  | .s3future => Data.ran_s3future | .s3nulls => Data.ran_s3nulls

/-- How `up` and `down` see `L`. -/
def views (s : Setting) (p : Prog) : M (Bounds × Bounds) := do
  let a ← boundsOf s ["A"] "L"
  let b ← boundsOf s ["B"] "L"
  let ab ← boundsOf s ["A", "B"] "L"
  pure (match p.view with | .two => (a, b) | .swapped => (b, a) | .inter => (ab, ab))

/-- The erasure of `L` with these upper bounds: `Int & String` erases to `Int`. -/
def erased (b : Bounds) : Ty :=
  if b.hi.contains .int then .int else if b.hi.contains .str then .str else .any

/-- The types claim the pushed `Int` is a `String` where erasure checks. -/
def claimsString (s : Setting) (p : Prog) : Bool :=
  match ex p.program.env (views s p) with
  | .ok (u, d) => p.out == .str || erased u == .str || erased d == .str
  | .error _ => false

/-- The named counterexamples: accepted, a `null` path, and a `String` claimed of an `Int`. -/
def Unsound (s : Setting) (p : Prog) : Bool := accepts s p && p.path.nullValued && claimsString s p

/-- **The model of each compiler's check is the compiler**, on every program of the space and every
setting: accepted, or rejected with the same first error by kind. -/
theorem calibrated : ∀ s ∈ Setting.all, space.map (fun p => (verdict s p).code) = compiled s := by
  decide +kernel

/-- **What the compilers accept and what runs.** On every program of the space and every setting, an
accepted program throws a `ClassCastException` exactly when it is `Unsound`, and a rejected program
was not run. -/
theorem accepted_sound_except : ∀ s ∈ Setting.all,
    (space.zip (ran s)).all (fun (p, r) => if accepts s p then (r == 2) == Unsound s p else r == 0) := by
  decide +kernel

/-- **Explicit nulls close the hole on this space**: no program accepted under `-Yexplicit-nulls`
throws a `ClassCastException`. -/
theorem nulls_no_cce : (ran .s3nulls).all (· != 2) := by decide +kernel

/-- How many: 48 accepted unsound programs under scalac 2.12 and 2.13, 264 under dotc 3.9 with or
without `-source future`, none with explicit nulls. -/
theorem unsound_counts :
    Setting.all.map (fun s => (space.filter (Unsound s)).length) = [48, 48, 264, 264, 0] := by
  decide +kernel

end Scala.Paths
