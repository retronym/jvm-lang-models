/-!
# Facts that grow: a read freezes them

Some facts are not pulled by a completer but pushed: a sealed class's children are registered as
each subclass's parents are typed, a companion link when the companion is entered. A read sees
whatever has been pushed so far, so its answer depends on the order in which the compiler typed
the rest of the program: scala/bug#7046 (`knownDirectSubclasses` empty, depending on file order),
scala/scala3#9069 (`Mirror.SumOf` across files).

dotc's guard (`ChildrenQueried`) makes a read freeze the fact: pushing to it afterwards is a hard
error ("children of … were already queried before … was discovered"). That is an LVar freeze
(Kuper and Newton, *Freeze after writing*), and the property it buys is quasi-determinism:

* `unguarded_diverges`: without the guard, two schedules of the same pushes give a read different
  answers, and nothing fails;
* `guarded_quasi_det`: with it, a schedule that completes reads the whole fact at every read, the
  same under every schedule. A schedule either gives the one answer or fails loudly.

dotc's fix for #9069 (scala/scala3#9083) goes further for sealed classes: before the first read it
completes every class that could be a child, so the pushes happen before any read.
-/

namespace Query.Freeze

variable {C : Type}

/-- A push of `c`, or a read of everything pushed so far. -/
inductive Ev (C : Type)
  | push (c : C)
  | read
  deriving DecidableEq, Repr

/-- Without a guard: every read returns what has been pushed so far. -/
def unguarded : List (Ev C) → List C → List (List C)
  | [], _ => []
  | .push c :: es, acc => unguarded es (c :: acc)
  | .read :: es, acc => acc :: unguarded es acc

/-- With the guard: a read freezes the fact, and a later push fails the run (`none`). -/
def guarded : List (Ev C) → List C → Bool → Option (List (List C))
  | [], _, _ => some []
  | .push c :: es, acc, frozen => if frozen then none else guarded es (c :: acc) frozen
  | .read :: es, acc, _ => (guarded es acc true).map (acc :: ·)

/-- After a freeze, a run that completes has no more pushes, and every read sees the same. -/
theorem guarded_frozen (es : List (Ev C)) (acc : List C) (outs : List (List C))
    (h : guarded es acc true = some outs) :
    (∀ c, Ev.push c ∉ es) ∧ ∀ o ∈ outs, o = acc := by
  induction es generalizing outs with
  | nil => simp [guarded] at h; subst h; simp
  | cons e es ih =>
    cases e with
    | push c => simp [guarded] at h
    | read =>
      simp only [guarded, Option.map_eq_some_iff] at h
      obtain ⟨outs', h', rfl⟩ := h
      obtain ⟨hp, ho⟩ := ih outs' h'
      refine ⟨fun c hc => ?_, fun o ho' => ?_⟩
      · simp only [List.mem_cons, reduceCtorEq, false_or] at hc; exact hp c hc
      · simp only [List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · rfl
        · exact ho o ho'

/-- **Quasi-determinism.** If a guarded run completes, every read saw every push of the
schedule (and what was there before): the answer is the whole fact, whatever the order. -/
theorem guarded_quasi_det (es : List (Ev C)) (acc : List C) (frozen : Bool)
    (outs : List (List C)) (h : guarded es acc frozen = some outs) :
    ∀ o ∈ outs, ∀ c, c ∈ o ↔ c ∈ acc ∨ Ev.push c ∈ es := by
  induction es generalizing acc frozen outs with
  | nil => simp [guarded] at h; subst h; simp
  | cons e es ih =>
    cases e with
    | push c' =>
      cases frozen with
      | true => simp [guarded] at h
      | false =>
        simp only [guarded, Bool.false_eq_true, ↓reduceIte] at h
        intro o ho c
        rw [ih (c' :: acc) false outs h o ho c]
        simp only [List.mem_cons, Ev.push.injEq]
        constructor
        · rintro ((rfl | h) | h) <;> simp_all
        · rintro (h | rfl | h) <;> simp_all
    | read =>
      simp only [guarded, Option.map_eq_some_iff] at h
      obtain ⟨outs', h', rfl⟩ := h
      obtain ⟨hp, ho⟩ := guarded_frozen es acc outs' h'
      intro o ho' c
      have hoacc : o = acc := by
        simp only [List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · rfl
        · exact ho o ho'
      subst hoacc
      simp only [List.mem_cons, reduceCtorEq, false_or]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h (hp c)

/-- **Without the guard, reads depend on the schedule**: the same two pushes, with the read in
between or after, give a read two answers, and nothing fails. -/
theorem unguarded_diverges :
    unguarded [.push "A", .read, .push "B"] [] ≠ unguarded [.push "A", .push "B", .read] [] := by
  decide

/-- With the guard, the first schedule fails loudly instead. -/
theorem guarded_fails : guarded [.push "A", .read, .push "B"] [] false = none := by decide

end Query.Freeze
