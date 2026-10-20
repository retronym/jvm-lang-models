import Query.Task
/-!
# Lazy evaluation of self-referential facts, and when it black-holes

A compiler's symbol table is a set of facts — a symbol's info, its parents, its members' types,
its flags at a phase — each defined by a task (`Query.Task`) that asks other facts. The compiler
evaluates them on demand and caches them: a fact is a *completer* until forced, then a value.
Forcing a fact that is already being forced is a cyclic reference (scalac's `LOCKED` flag, dotc's
`Touched`), a black hole.

* `force` is that evaluator: a store of finished facts, a stack of facts in progress, and the rules.
* `Fix` and `Ranked` say what the *semantics* is: a valuation `ρ` that is a fixed point of the rules,
  and a rank that strictly decreases along every query a rule asks under `ρ`. A ranked fixed point
  is a set of definitions whose dependencies are well-founded: recursion through them may still go
  through a fact by name (a type constructor), but never through its value.
* **`force_ok`**: with a ranked fixed point, forcing any fact from any consistent store returns its
  value, and never black-holes. **`forceAll_ok`**: so every order of demands gives the same answers.
  Laziness is what makes a well-founded set of definitions evaluable at all, in any order.
* A black hole therefore means: no ranking of *these rules* exists (`cycle_unranked`). Whether that
  is a property of the program (a *true* cycle) or of how the compiler cut the facts into rules
  (a *spurious* one) is the question of `Query.Lazy.Bundle` and of the compiler-shaped witnesses in
  `ScalaTypes.Laziness`.
-/

namespace Query.Lazy

variable {Q V : Type} [DecidableEq Q]

/-- The rule of each fact: a task asking other facts, all of value type `V`. -/
abbrev Rules (Q V : Type) := Q → Task Q (fun _ => V) V

/-- The finished facts. -/
abbrev Store (Q V : Type) := Q → Option V

/-- The outcome of forcing: a value, a black hole at a fact (a cyclic reference), or out of fuel. -/
inductive Out (Q V : Type)
  | ok (v : V)
  | cyc (q : Q)
  | fuel
  deriving DecidableEq, Repr

def upd (s : Store Q V) (q : Q) (v : V) : Store Q V := fun q' => if q' = q then some v else s q'

/-- Run a task, forcing each fact it asks with `f`; stops at the first failure. -/
def runWith (f : Store Q V → Q → Out Q V × Store Q V) :
    Task Q (fun _ => V) V → Store Q V → Out Q V × Store Q V
  | .pure v, s => (.ok v, s)
  | .ask q k, s =>
    match f s q with
    | (.ok v, s') => runWith f (k v) s'
    | (e, s') => (e, s')

/-- Force fact `q`: a finished fact is read from the store; a fact already in progress (on the
stack) is a black hole; otherwise its rule runs with `q` pushed, and the value is stored. -/
def force (R : Rules Q V) : Nat → List Q → Store Q V → Q → Out Q V × Store Q V
  | 0, _, s, _ => (.fuel, s)
  | n + 1, stk, s, q =>
    match s q with
    | some v => (.ok v, s)
    | none =>
      if q ∈ stk then (.cyc q, s)
      else
        match runWith (fun s' q' => force R n (q :: stk) s' q') (R q) s with
        | (.ok v, s') => (.ok v, upd s' q v)
        | (e, s') => (e, s')

/-! ## The semantics: ranked fixed points -/

/-- `ρ` is a fixed point of the rules: each fact is what its rule computes from the others. -/
def Fix (R : Rules Q V) (ρ : Q → V) : Prop := ∀ q, ρ q = (R q).run ρ

/-- A rank that decreases along every fact a rule asks under `ρ`: the definitions are
well-founded. -/
def Ranked (R : Rules Q V) (ρ : Q → V) (r : Q → Nat) : Prop :=
  ∀ q, ∀ q' ∈ (R q).trace ρ, r q' < r q

/-- A store agrees with `ρ` on what it has finished. -/
def Agree (ρ : Q → V) (s : Store Q V) : Prop := ∀ q v, s q = some v → v = ρ q

/-- `s'` keeps everything `s` finished. -/
def Ext (s s' : Store Q V) : Prop := ∀ q v, s q = some v → s' q = some v

omit [DecidableEq Q] in
theorem Ext.refl (s : Store Q V) : Ext s s := fun _ _ h => h
omit [DecidableEq Q] in
theorem Ext.trans {s₁ s₂ s₃ : Store Q V} (a : Ext s₁ s₂) (b : Ext s₂ s₃) : Ext s₁ s₃ :=
  fun q v h => b q v (a q v h)

omit [DecidableEq Q] in
/-- Running a task whose asked facts all force correctly gives the task's value under `ρ`. -/
theorem runWith_ok (ρ : Q → V) (f : Store Q V → Q → Out Q V × Store Q V)
    (t : Task Q (fun _ => V) V)
    (hf : ∀ q ∈ t.trace ρ, ∀ s, Agree ρ s → ∃ s', f s q = (.ok (ρ q), s') ∧ Agree ρ s' ∧ Ext s s') :
    ∀ s, Agree ρ s → ∃ s', runWith f t s = (.ok (t.run ρ), s') ∧ Agree ρ s' ∧ Ext s s' := by
  induction t with
  | pure v => intro s hs; exact ⟨s, rfl, hs, Ext.refl s⟩
  | ask q k ih =>
    intro s hs
    obtain ⟨s₁, h₁, a₁, e₁⟩ := hf q (by simp [Task.trace]) s hs
    have hk : ∀ q' ∈ (k (ρ q)).trace ρ, ∀ s, Agree ρ s →
        ∃ s', f s q' = (.ok (ρ q'), s') ∧ Agree ρ s' ∧ Ext s s' :=
      fun q' hq' => hf q' (by simp [Task.trace, hq'])
    obtain ⟨s₂, h₂, a₂, e₂⟩ := ih (ρ q) hk s₁ a₁
    refine ⟨s₂, ?_, a₂, e₁.trans e₂⟩
    simp only [runWith, h₁, Task.run]
    exact h₂

/-- **Laziness is sound.** With a ranked fixed point, forcing a fact whose rank is below the
fuel, from a store that agrees with `ρ`, with every fact in progress ranked above it, returns its
value under `ρ`; it never black-holes. -/
theorem force_ok (R : Rules Q V) (ρ : Q → V) (r : Q → Nat) (hfix : Fix R ρ) (hr : Ranked R ρ r) :
    ∀ n q stk s, r q < n → Agree ρ s → (∀ x ∈ stk, r q < r x) →
      ∃ s', force R n stk s q = (.ok (ρ q), s') ∧ Agree ρ s' ∧ Ext s s' := by
  intro n
  induction n with
  | zero => intro q _ _ h; omega
  | succ n ih =>
    intro q stk s hn hs hstk
    cases hsq : s q with
    | some v =>
      refine ⟨s, ?_, hs, Ext.refl s⟩
      simp only [force, hsq]
      rw [hs q v hsq]
    | none =>
      have hnot : q ∉ stk := fun hm => by have := hstk q hm; omega
      have hrun := runWith_ok ρ (fun s' q' => force R n (q :: stk) s' q') (R q)
        (fun q' hq' s' hs' => ih q' (q :: stk) s' (by have := hr q q' hq'; omega) hs'
          (by
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hr x q' hq'
            · have := hr q q' hq'; have := hstk x hx; omega)) s hs
      obtain ⟨s', h', a', e'⟩ := hrun
      refine ⟨upd s' q (ρ q), ?_, ?_, ?_⟩
      · simp only [force, hsq, hnot, ↓reduceIte, h']
        rw [← hfix q]
      · intro x v hx
        simp only [upd] at hx
        split at hx
        · subst_vars; injection hx with hx; exact hx.symm
        · exact a' x v hx
      · intro x v hx
        simp only [upd]
        split
        · subst_vars; rw [hsq] at hx; cases hx
        · exact e' x v hx

/-- Force a list of facts in order, threading the store; the first failure stops. -/
def forceAll (R : Rules Q V) (n : Nat) : List Q → Store Q V → List (Out Q V) × Store Q V
  | [], s => ([], s)
  | q :: qs, s =>
    let (o, s₁) := force R n [] s q
    let (os, s₂) := forceAll R n qs s₁
    (o :: os, s₂)

/-- **Any order of demands gives the same answers**: forcing any list of facts, in any order,
from an empty store, gives each its value under `ρ`. The compiler's answer to a well-founded set
of definitions does not depend on which file it typechecks first. -/
theorem forceAll_ok (R : Rules Q V) (ρ : Q → V) (r : Q → Nat) (hfix : Fix R ρ) (hr : Ranked R ρ r)
    (n : Nat) (qs : List Q) (hn : ∀ q ∈ qs, r q < n) :
    ∀ s, Agree ρ s → (forceAll R n qs s).1 = qs.map fun q => .ok (ρ q) := by
  induction qs with
  | nil => intro s _; rfl
  | cons q qs ih =>
    intro s hs
    obtain ⟨s₁, h₁, a₁, _⟩ :=
      force_ok R ρ r hfix hr n q [] s (hn q (by simp)) hs (by simp)
    simp only [forceAll, h₁, List.map_cons]
    rw [ih (fun q' hq' => hn q' (by simp [hq'])) s₁ a₁]

/-- **A black hole means there is no ranking of these rules** with the fact below the fuel: if
forcing `q` from an empty store black-holes or runs out of fuel `n`, every ranked fixed point
ranks `q` at `n` or more. With finitely many facts a ranking can be taken below their number, so
for enough fuel a black hole says the rules are not well-founded. -/
theorem cycle_unranked (R : Rules Q V) (n : Nat) (q : Q)
    (h : ∀ v, (force R n [] (fun _ => none) q).1 ≠ .ok v) :
    ∀ ρ r, Fix R ρ → Ranked R ρ r → n ≤ r q := by
  intro ρ r hfix hr
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨s', h', _, _⟩ := force_ok R ρ r hfix hr n q [] (fun _ => none) hlt
    (fun _ _ h => by cases h) (by simp)
  exact h (ρ q) (by rw [h'])

/-! ## Facts indexed by phase

A compiler asks a fact *at a phase*: a symbol's info as typer saw it, as erasure sees it, its name
before and after flatten. Phase `p + 1`'s fact is the `p`th transformer applied to phase `p`'s,
which may read other facts at phase `p + 1` or earlier (erasure reads the erased parents).
scalac extends a symbol's `TypeHistory` this way when a later phase reads it (`transformInfos`),
dotc a denotation's `nextInRun` chain (`SingleDenotation.current`).

`phase_ranked`: if no fact reads a later phase, and within a phase the reads are ranked (below a
bound `K`), the whole system is ranked, so `force_ok` applies: phase-indexed laziness is sound
and order-independent. The rank is lexicographic, phase first. -/

/-- **Phases rank lexicographically.** Facts `(x, p)`; every fact asked is at an earlier phase, or
at the same phase with a smaller rank there (all ranks below `K`). -/
theorem phase_ranked {X : Type} [DecidableEq X] (R : Rules (X × Nat) V) (ρ : X × Nat → V)
    (r : Nat → X → Nat) (K : Nat) (hK : ∀ p x, r p x < K)
    (h : ∀ x p, ∀ q' ∈ (R (x, p)).trace ρ, q'.2 < p ∨ (q'.2 = p ∧ r p q'.1 < r p x)) :
    Ranked R ρ (fun q => q.2 * K + r q.2 q.1) := by
  intro ⟨x, p⟩ ⟨y, p'⟩ hq
  rcases h x p (y, p') hq with hlt | ⟨heq, hlt⟩
  · have h1 : r p' y < K := hK p' y
    have h2 : (p' + 1) * K ≤ p * K := Nat.mul_le_mul_right K hlt
    simp only [Nat.succ_mul] at h2
    simp only
    omega
  · simp only at heq hlt ⊢
    subst heq
    omega

end Query.Lazy
