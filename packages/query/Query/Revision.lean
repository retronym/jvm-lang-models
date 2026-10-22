import Query.Lazy
/-!
# Revisions: facts that outlive a run, re-validated by their traces

A presentation compiler's facts (`Query.Lazy`) live in a run; an edit starts a new run and the
facts are recomputed, whole file at a time (dotc) or by symbol identity (scalac). The alternative
is a store per *revision*, each fact kept with the facts its rule asked (its trace), and a fact of
revision `r` reused at `r + 1` when the new oracle agrees with the old on that trace: T1,
[`Query.Task.run_eq_of_trace`](Task.lean). This is Adapton's and Salsa's "verify by dependencies"
over `Query.Lazy.force`: `reval` is `force` with one more branch, and the deps are checked in the
order the rule asked them, since a dependency after a changed one may not have been asked at all
under the new oracle (`mem_trace_of_agree_prefix`). A dependency whose recomputed value equals its
old one is as good as unchanged: backdating comes for free from comparing values rather than
revisions.

`reuse_sound`: from a store of revision `r` that agrees with `r`'s fixed point, with the rules
of `r + 1` ranked, re-validation returns `r + 1`'s value for every fact and leaves a store that
agrees with `r + 1`'s fixed point, with each entry's recorded trace that of `r + 1`. The hypothesis
on the edit (`Same`) is semantic: a fact the edit is said to leave alone has an old rule that,
under the new oracle, gives the new value and asks the same facts. How a compiler knows that is
its business (node identity in a tree, name hashing, a modification tracker); the toy's trees
(`ScalaTypes.ToyTree`) supply it per edit.
-/

namespace Query.Task

variable {Q : Type} {A : Q → Type} {α : Type}

/-- A query in a trace is still asked under another oracle that agrees on the queries before it:
the first query is asked whatever the oracle, and each later one is decided by the answers so
far. -/
theorem mem_trace_of_agree_prefix (t : Task Q A α) (e e' : Env Q A) :
    ∀ pre x post, t.trace e = pre ++ x :: post → (∀ y ∈ pre, e y = e' y) → x ∈ t.trace e' := by
  induction t with
  | pure a => intro pre x post h; simp at h
  | ask q k ih =>
    intro pre x post h hpre
    cases pre with
    | nil =>
      simp only [trace_ask, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp
    | cons y pre =>
      simp only [trace_ask, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have hq : e q = e' q := hpre q (by simp)
      simp only [trace_ask, List.mem_cons]
      right
      rw [← hq]
      exact ih (e q) pre x post h (fun z hz => hpre z (by simp [hz]))

end Query.Task

namespace Query.Revision

open Query.Lazy

variable {Q V : Type} [DecidableEq Q] [DecidableEq V]

/-- A finished fact: its value, the facts its rule asked, the revision since which it has had this
value (a reused entry keeps its `since`, dotc's `validFor` extended by `bringForward`; so does a
recomputed one whose value came out equal, Salsa's backdating), and the revision that last ran its
rule, which is the work done. -/
structure Entry (Q V : Type) where
  value : V
  deps : List Q
  since : Nat
  computed : Nat
  deriving DecidableEq, Repr

/-- The store of a revision. -/
abbrev Memo (Q V : Type) := Store Q (Entry Q V)

def empty : Memo Q V := fun _ => none

/-- Run a task, forcing each fact it asks with `f`, and record the facts asked. -/
def runWithT (f : Memo Q V → Q → Out Q V × Memo Q V) :
    Task Q (fun _ => V) V → Memo Q V → Out Q V × List Q × Memo Q V
  | .pure v, m => (.ok v, [], m)
  | .ask q k, m =>
    match f m q with
    | (.ok v, m') =>
      match runWithT f (k v) m' with
      | (o, tr, m'') => (o, q :: tr, m'')
    | (e, m') => (e, [], m')

/-- Check an old entry's deps in order: each is forced (re-validated in turn) and compared with
its old value; the first that differs, or that the old store lacks, ends the check. -/
def checkDeps (f : Memo Q V → Q → Out Q V × Memo Q V) (old : Memo Q V) :
    List Q → Memo Q V → Out Q Bool × Memo Q V
  | [], m => (.ok true, m)
  | d :: ds, m =>
    match f m d with
    | (.ok v, m') =>
      match old d with
      | some e => if e.value = v then checkDeps f old ds m' else (.ok false, m')
      | none => (.ok false, m')
    | (.cyc x, m') => (.cyc x, m')
    | (.fuel, m') => (.fuel, m')

/-- Compute `q` from its rule, storing the value with its trace at revision `rev`; a value equal
to the old revision's keeps that revision's `since`. -/
def recomputeWith (f : Memo Q V → Q → Out Q V × Memo Q V) (R : Rules Q V) (old : Memo Q V)
    (rev : Nat) (q : Q) (m : Memo Q V) : Out Q V × Memo Q V :=
  match runWithT f (R q) m with
  | (.ok v, tr, m') =>
    let since := match old q with | some e => if e.value = v then e.since else rev | none => rev
    (.ok v, upd m' q ⟨v, tr, since, rev⟩)
  | (e, _, m') => (e, m')

/-- Force `q` at revision `rev` with rules `R`, over the store `old` of the previous revision:
a fact already finished in this revision is read; a fact in progress is a black hole; a fact of
the old store whose rule the edit left alone (`same q`) is reused if every dep still has its old
value, each dep re-validated first; otherwise its rule runs. -/
def reval (R : Rules Q V) (same : Q → Bool) (old : Memo Q V) (rev : Nat) :
    Nat → List Q → Memo Q V → Q → Out Q V × Memo Q V
  | 0, _, m, _ => (.fuel, m)
  | n + 1, stk, m, q =>
    match m q with
    | some e => (.ok e.value, m)
    | none =>
      if q ∈ stk then (.cyc q, m)
      else
        match old q with
        | some e =>
          if same q then
            match checkDeps (fun m' q' => reval R same old rev n (q :: stk) m' q') old e.deps m with
            | (.ok true, m') => (.ok e.value, upd m' q e)
            | (.ok false, m') =>
              recomputeWith (fun m' q' => reval R same old rev n (q :: stk) m' q') R old rev q m'
            | (.cyc x, m') => (.cyc x, m')
            | (.fuel, m') => (.fuel, m')
          else recomputeWith (fun m' q' => reval R same old rev n (q :: stk) m' q') R old rev q m
        | none => recomputeWith (fun m' q' => reval R same old rev n (q :: stk) m' q') R old rev q m

/-- A session: requests in order on one revision, threading the store. -/
def revalAll (R : Rules Q V) (same : Q → Bool) (old : Memo Q V) (rev : Nat) (n : Nat) :
    List Q → Memo Q V → List (Out Q V) × Memo Q V
  | [], m => ([], m)
  | q :: qs, m =>
    let (o, m₁) := reval R same old rev n [] m q
    let (os, m₂) := revalAll R same old rev n qs m₁
    (o :: os, m₂)

/-- A fresh store: no previous revision. -/
def fresh (R : Rules Q V) (rev n : Nat) (qs : List Q) : List (Out Q V) × Memo Q V :=
  revalAll R (fun _ => false) empty rev n qs empty

/-- The facts of `qs` whose rules revision `rev` ran: its work. -/
def computedAt (m : Memo Q V) (rev : Nat) (qs : List Q) : List Q :=
  qs.filter fun q => match m q with | some e => e.computed == rev | none => false

/-- The facts of `qs` whose values revision `rev` changed (or first computed): what it invalidated
for the revisions after it. -/
def changedAt (m : Memo Q V) (rev : Nat) (qs : List Q) : List Q :=
  qs.filter fun q => match m q with | some e => e.since == rev | none => false

/-! ## Soundness -/

/-- A store agrees with the semantics `ρ` of rules `R`: each entry holds the value and the trace
under `ρ`. -/
def AgreeM (R : Rules Q V) (ρ : Q → V) (m : Memo Q V) : Prop :=
  ∀ q e, m q = some e → e.value = ρ q ∧ e.deps = (R q).trace ρ

/-- The edit left `q`'s rule alone, semantically: under the new oracle, the old rule gives the
new rule's value and asks the same facts. -/
def Same (R R' : Rules Q V) (ρ' : Q → V) (same : Q → Bool) : Prop :=
  ∀ q, same q = true → (R q).run ρ' = (R' q).run ρ' ∧ (R q).trace ρ' = (R' q).trace ρ'

omit [DecidableEq Q] [DecidableEq V] in
theorem runWithT_ok (ρ : Q → V) (f : Memo Q V → Q → Out Q V × Memo Q V) (P : Memo Q V → Prop)
    (t : Task Q (fun _ => V) V)
    (hf : ∀ q ∈ t.trace ρ, ∀ m, P m → ∃ m', f m q = (.ok (ρ q), m') ∧ P m' ∧ Ext m m') :
    ∀ m, P m → ∃ m', runWithT f t m = (.ok (t.run ρ), t.trace ρ, m') ∧ P m' ∧ Ext m m' := by
  induction t with
  | pure v => intro m hm; exact ⟨m, rfl, hm, Ext.refl m⟩
  | ask q k ih =>
    intro m hm
    obtain ⟨m₁, h₁, p₁, e₁⟩ := hf q (by simp [Task.trace]) m hm
    have hk : ∀ q' ∈ (k (ρ q)).trace ρ, ∀ m, P m →
        ∃ m', f m q' = (.ok (ρ q'), m') ∧ P m' ∧ Ext m m' :=
      fun q' hq' => hf q' (by simp [Task.trace, hq'])
    obtain ⟨m₂, h₂, p₂, e₂⟩ := ih (ρ q) hk m₁ p₁
    refine ⟨m₂, ?_, p₂, e₁.trans e₂⟩
    simp only [runWithT, h₁, h₂, Task.run, Task.trace]

omit [DecidableEq Q] in
/-- Checking the deps of a rule's old trace in order: every dep checked is one the rule asks under
the new oracle too, and a check that passes says the two oracles agree on the whole trace. -/
theorem checkDeps_ok (ρ ρ' : Q → V) (f : Memo Q V → Q → Out Q V × Memo Q V) (P : Memo Q V → Prop)
    (old : Memo Q V) (t : Task Q (fun _ => V) V)
    (hold : ∀ d e, old d = some e → e.value = ρ d)
    (hf : ∀ d ∈ t.trace ρ', ∀ m, P m → ∃ m', f m d = (.ok (ρ' d), m') ∧ P m' ∧ Ext m m') :
    ∀ pre ds, t.trace ρ = pre ++ ds → (∀ y ∈ pre, ρ' y = ρ y) → ∀ m, P m →
      ∃ m' b, checkDeps f old ds m = (.ok b, m') ∧ P m' ∧ Ext m m' ∧
        (b = true → ∀ y ∈ ds, ρ' y = ρ y) := by
  intro pre ds
  induction ds generalizing pre with
  | nil => intro _ _ m hm; exact ⟨m, true, rfl, hm, Ext.refl m, fun _ y hy => by simp at hy⟩
  | cons d ds ih =>
    intro h hpre m hm
    have hd : d ∈ t.trace ρ' :=
      Task.mem_trace_of_agree_prefix t ρ ρ' pre d ds h (fun y hy => (hpre y hy).symm)
    obtain ⟨m₁, h₁, p₁, e₁⟩ := hf d hd m hm
    cases hod : old d with
    | none =>
      exact ⟨m₁, false, by simp only [checkDeps, h₁, hod], p₁, e₁, fun h => by cases h⟩
    | some e =>
      have he : e.value = ρ d := hold d e hod
      by_cases heq : e.value = ρ' d
      · have hagree : ρ' d = ρ d := heq.symm.trans he
        obtain ⟨m₂, b, h₂, p₂, e₂, hb⟩ := ih (pre ++ [d]) (by rw [h, List.append_assoc]; rfl)
          (fun y hy => by
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hpre y hy
            · exact hagree) m₁ p₁
        refine ⟨m₂, b, ?_, p₂, e₁.trans e₂, ?_⟩
        · simp only [checkDeps, h₁, hod, heq, ↓reduceIte, h₂]
        · intro hb' y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hagree
          · exact hb hb' y hy
      · exact ⟨m₁, false, by simp only [checkDeps, h₁, hod, heq, ↓reduceIte], p₁, e₁,
          fun h => by cases h⟩

/-- **Re-validation by trace is sound.** Revision `r` had rules `R` with fixed point `ρ` and left
a store `old` that agrees with it; revision `r + 1` has rules `R'` with a ranked fixed point `ρ'`;
the edit leaves alone the rules of the facts `same` says (`Same`). Then re-validating any fact,
from any store that agrees with `ρ'`, returns its value under `ρ'`, never black-holes, and leaves
a store that agrees with `ρ'`, traces included. A reused entry is correct because its deps were
re-validated first, in order, and found equal to their old values, so T1 carries its old value
across the edit. -/
theorem reuse_sound (R R' : Rules Q V) (ρ ρ' : Q → V) (r : Q → Nat) (same : Q → Bool)
    (old : Memo Q V) (rev : Nat)
    (hfixold : Fix R ρ) (hfix : Fix R' ρ') (hr : Ranked R' ρ' r)
    (hold : AgreeM R ρ old) (hsame : Same R R' ρ' same) :
    ∀ n q stk m, r q < n → AgreeM R' ρ' m → (∀ x ∈ stk, r q < r x) →
      ∃ m', reval R' same old rev n stk m q = (.ok (ρ' q), m') ∧ AgreeM R' ρ' m' ∧ Ext m m' := by
  intro n
  induction n with
  | zero => intro q _ _ h; omega
  | succ n ih =>
    intro q stk m hn hm hstk
    cases hmq : m q with
    | some e =>
      refine ⟨m, ?_, hm, Ext.refl m⟩
      simp only [reval, hmq]
      rw [(hm q e hmq).1]
    | none =>
      have hnot : q ∉ stk := fun hmem => by have := hstk q hmem; omega
      -- the deps of `q` under the new oracle re-validate to their new values
      have hf : ∀ q' ∈ (R' q).trace ρ', ∀ m, AgreeM R' ρ' m →
          ∃ m', reval R' same old rev n (q :: stk) m q' = (.ok (ρ' q'), m') ∧ AgreeM R' ρ' m' ∧ Ext m m' :=
        fun q' hq' m hm => ih q' (q :: stk) m (by have := hr q q' hq'; omega) hm
          (by
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hr x q' hq'
            · have := hr q q' hq'; have := hstk x hx; omega)
      -- recomputing from any store reached so far is `force_ok`'s argument
      have hrec : ∀ m₁, AgreeM R' ρ' m₁ → Ext m m₁ →
          ∃ m', recomputeWith (fun m' q' => reval R' same old rev n (q :: stk) m' q') R' old rev q m₁ =
            (.ok (ρ' q), m') ∧ AgreeM R' ρ' m' ∧ Ext m m' := by
        intro m₁ hm₁ hext
        obtain ⟨m₂, h₂, p₂, e₂⟩ := runWithT_ok ρ' _ (AgreeM R' ρ') (R' q) hf m₁ hm₁
        refine ⟨upd m₂ q ⟨(R' q).run ρ', (R' q).trace ρ',
          match old q with | some e => if e.value = (R' q).run ρ' then e.since else rev | none => rev, rev⟩,
          ?_, ?_, ?_⟩
        · simp only [recomputeWith, h₂]
          rw [← hfix q]
        · intro x e hx
          simp only [upd] at hx
          split at hx
          · subst_vars; injection hx with hx; subst hx; exact ⟨(hfix _).symm, rfl⟩
          · exact p₂ x e hx
        · intro x v hx
          simp only [upd]
          split
          · subst_vars; rw [hmq] at hx; cases hx
          · exact (hext.trans e₂) x v hx
      cases hoq : old q with
      | none =>
        simp only [reval, hmq, hnot, ↓reduceIte, hoq]
        exact hrec m hm (Ext.refl m)
      | some e =>
        by_cases hs : same q = true
        · obtain ⟨hrun, htr⟩ := hsame q hs
          obtain ⟨hval, hdeps⟩ := hold q e hoq
          have hf' : ∀ d ∈ (R q).trace ρ', ∀ m, AgreeM R' ρ' m →
              ∃ m', reval R' same old rev n (q :: stk) m d = (.ok (ρ' d), m') ∧ AgreeM R' ρ' m' ∧ Ext m m' := by
            rw [htr]; exact hf
          obtain ⟨m₁, b, hc, p₁, e₁, hb⟩ := checkDeps_ok ρ ρ' _ (AgreeM R' ρ') old (R q)
            (fun d e hd => (hold d e hd).1) hf' [] e.deps (by rw [hdeps]; rfl) (by simp) m hm
          cases b with
          | true =>
            have hagree : ∀ y ∈ (R q).trace ρ, ρ y = ρ' y :=
              fun y hy => (hb rfl y (hdeps ▸ hy)).symm
            obtain ⟨hr1, ht1⟩ := Task.run_eq_of_trace (R q) ρ ρ' hagree
            have hv : e.value = ρ' q := by
              rw [hval, hfixold q, hr1, hrun, ← hfix q]
            have hd : e.deps = (R' q).trace ρ' := by rw [hdeps, ht1, htr]
            refine ⟨upd m₁ q e, ?_, ?_, ?_⟩
            · simp only [reval, hmq, hnot, ↓reduceIte, hoq, hs, hc]
              rw [hv]
            · intro x e' hx
              simp only [upd] at hx
              split at hx
              · subst_vars; injection hx with hx; subst hx; exact ⟨hv, hd⟩
              · exact p₁ x e' hx
            · intro x v hx
              simp only [upd]
              split
              · subst_vars; rw [hmq] at hx; cases hx
              · exact e₁ x v hx
          | false =>
            obtain ⟨m', h', p', e'⟩ := hrec m₁ p₁ e₁
            refine ⟨m', ?_, p', e'⟩
            simp only [reval, hmq, hnot, ↓reduceIte, hoq, hs, hc]
            exact h'
        · have hs' : same q = false := Bool.eq_false_iff.mpr hs
          simp only [reval, hmq, hnot, ↓reduceIte, hoq, hs', Bool.false_eq_true]
          exact hrec m hm (Ext.refl m)

/-- **A session is a fresh run, request for request.** Any sequence of requests on one revision,
from any store that agrees with its fixed point (the store left by earlier requests of the
session, or by re-validation), gives each request its value under `ρ'`, which is what the request
alone on a fresh store gives. `forceAll_ok` over `reval`. -/
theorem session_eq_fresh (R R' : Rules Q V) (ρ ρ' : Q → V) (r : Q → Nat) (same : Q → Bool)
    (old : Memo Q V) (rev : Nat)
    (hfixold : Fix R ρ) (hfix : Fix R' ρ') (hr : Ranked R' ρ' r)
    (hold : AgreeM R ρ old) (hsame : Same R R' ρ' same)
    (n : Nat) (qs : List Q) (hn : ∀ q ∈ qs, r q < n) :
    ∀ m, AgreeM R' ρ' m →
      (revalAll R' same old rev n qs m).1 = qs.map (fun q => Out.ok (ρ' q)) ∧
      (fresh R' rev n qs).1 = qs.map (fun q => Out.ok (ρ' q)) := by
  have gen : ∀ (same : Q → Bool) (old : Memo Q V) (R : Rules Q V) (ρ : Q → V), Fix R ρ → AgreeM R ρ old →
      Same R R' ρ' same → ∀ qs, (∀ q ∈ qs, r q < n) → ∀ m, AgreeM R' ρ' m →
      (revalAll R' same old rev n qs m).1 = qs.map (fun q => Out.ok (ρ' q)) := by
    intro same old R ρ hfixold hold hsame qs
    induction qs with
    | nil => intro _ m _; rfl
    | cons q qs ih =>
      intro hn m hm
      obtain ⟨m₁, h₁, a₁, _⟩ :=
        reuse_sound R R' ρ ρ' r same old rev hfixold hfix hr hold hsame n q [] m (hn q (by simp)) hm (by simp)
      simp only [revalAll, h₁, List.map_cons]
      rw [ih (fun q' hq' => hn q' (by simp [hq'])) m₁ a₁]
  intro m hm
  refine ⟨gen same old R ρ hfixold hold hsame qs hn m hm, ?_⟩
  exact gen (fun _ => false) empty R' ρ' hfix (fun _ _ h => by cases h) (fun _ h => by cases h) qs hn
    empty (fun _ _ h => by cases h)

end Query.Revision
