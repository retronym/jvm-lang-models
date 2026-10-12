import Query.Task
/-!
# Interpreting one query interface in another

A task over one query interface runs over another when each of its queries is given as a task
there: `interp f t` replaces every `ask q` of `t` by `f q`. Running the result is running `t`
against the oracle that answers `q` by running `f q`, and its trace is each query's trace under
`f`, in order. Renaming queries (`rename`) is the case where `f q` asks one query.

A shared model states its tasks over its own queries (`Scala.Q`); a consumer with its own query
shape (a framework's `unit × query`, or finer queries a bridge keys on) maps them in with `interp`
and reads its keys off the trace through `trace_interp`.
-/

namespace Query.Task

variable {Q Q' : Type} {A : Q → Type} {A' : Q' → Type} {α : Type}

/-- Replace each query `q` of a task by the task `f q`. -/
def interp (f : (q : Q) → Task Q' A' (A q)) : Task Q A α → Task Q' A' α
  | .pure a => .pure a
  | .ask q k => (f q).bind fun a => interp f (k a)

/-- The oracle a task sees through `interp f`: each query answered by running `f q`. -/
def Env.through (f : (q : Q) → Task Q' A' (A q)) (e : Env Q' A') : Env Q A :=
  fun q => (f q).run e

@[simp] theorem interp_pure (f : (q : Q) → Task Q' A' (A q)) (a : α) :
    interp f (.pure a) = .pure a := rfl

@[simp] theorem interp_ask (f : (q : Q) → Task Q' A' (A q)) (q : Q) (k : A q → Task Q A α) :
    interp f (.ask q k) = (f q).bind fun a => interp f (k a) := rfl

theorem run_interp (f : (q : Q) → Task Q' A' (A q)) (e : Env Q' A') :
    ∀ t : Task Q A α, (interp f t).run e = t.run (Env.through f e)
  | .pure _ => rfl
  | .ask q k => by
    simp only [interp_ask, run_bind, run_ask, Env.through]
    exact run_interp f e (k _)

/-- The trace through `interp f`: each query's own trace under `f`, in order. -/
theorem trace_interp (f : (q : Q) → Task Q' A' (A q)) (e : Env Q' A') :
    ∀ t : Task Q A α,
      (interp f t).trace e = (t.trace (Env.through f e)).flatMap fun q => (f q).trace e
  | .pure _ => rfl
  | .ask q k => by
    simp only [interp_ask, trace_bind, trace_ask, List.flatMap_cons]
    exact congrArg _ (trace_interp f e (k _))

theorem mem_trace_interp (f : (q : Q) → Task Q' A' (A q)) (e : Env Q' A') (t : Task Q A α)
    (q' : Q') :
    q' ∈ (interp f t).trace e ↔
      ∃ q ∈ t.trace (Env.through f e), q' ∈ (f q).trace e := by
  rw [trace_interp, List.mem_flatMap]

/-! ## Renaming -/

/-- Rename each query `q` to `g q`, transporting the answer back by `h q`. -/
def rename (g : Q → Q') (h : (q : Q) → A' (g q) → A q) : Task Q A α → Task Q' A' α :=
  interp fun q => .ask (g q) fun a => .pure (h q a)

theorem run_rename (g : Q → Q') (h : (q : Q) → A' (g q) → A q) (e : Env Q' A')
    (t : Task Q A α) : (rename g h t).run e = t.run fun q => h q (e (g q)) :=
  run_interp _ e t

theorem trace_rename (g : Q → Q') (h : (q : Q) → A' (g q) → A q) (e : Env Q' A')
    (t : Task Q A α) : (rename g h t).trace e = (t.trace fun q => h q (e (g q))).map g := by
  rw [rename, trace_interp]
  rw [List.map_eq_flatMap]; rfl

end Query.Task
