import AsSeenFrom.Scalac

/-!
# Chains of links versus one `asSeenFrom`

IntelliJ types a member by a chain of substitutor links `(p₁,c₁) >> (p₂,c₂) >> …`,
each one an anchored walk. This file proves when that chain is one `asSeenFrom`.

The one assumption about the world is **lockstep**: an `asSeenFrom` map commutes with
taking the base-type prefix. scalac relies on this (base types of a mapped type are
the mapped base types); in IntelliJ it is the contract `BaseTypes.baseType` must meet,
and the TCK's baseType dimension checks it empirically.
-/

namespace Chain
open Scalac

variable (W : World)

/-- Lockstep: `asSeenFrom` commutes with `bpre` and preserves `hasBase`. -/
class Lockstep : Prop where
  bpre_comm    : ∀ p₂ c₂ p c, asf W p₂ c₂ (W.bpre p c) = W.bpre (asf W p₂ c₂ p) c
  hasBase_comm : ∀ p₂ c₂ p c, W.hasBase (asf W p₂ c₂ p) c = W.hasBase p c

variable [Lockstep W]

/-- Rewriting is decided by the prefix's base types, which a later map preserves. -/
theorem rewrites_asf (d c : Class) (p₂ : Ty) (c₂ : Class) (p : Ty) :
    rewrites W d c (asf W p₂ c₂ p) = rewrites W d c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    simp only [rewrites, Lockstep.hasBase_comm]
    split
    · rfl
    · rw [← Lockstep.bpre_comm]; exact ih _

/-- The key lemma: a this-leaf that the first walk rewrites can be viewed again by a
second map, and the result is the first walk over the mapped prefix. -/
theorem thisAsSeen_asf (d c : Class) (p₂ : Ty) (c₂ : Class) (p : Ty)
    (h : rewrites W d c p = true) :
    asf W p₂ c₂ (thisAsSeen W d c p) = thisAsSeen W d c (asf W p₂ c₂ p) := by
  induction c generalizing p with
  | nil => simp [rewrites] at h
  | cons x rest ih =>
    simp only [thisAsSeen, rewrites, Lockstep.hasBase_comm] at h ⊢
    by_cases hc : (decide (x :: rest = d) && W.hasBase p (x :: rest)) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc] at h ⊢
      rw [← Lockstep.bpre_comm]
      exact ih _ h

/--
**Composition law (L).** Two maps in sequence are one map whose prefix is the first
prefix as seen by the second map, provided the first map rewrote every this-leaf of
the input (the input was in the view the first map resolves).

Note what the law does *not* need: no condition on `c₂`. Any second anchor gives some
single map; the anchor decides *which prefix* that map views from. `c₂` is correct
exactly when `asf p₂ c₂ p₁` is the intended "p₁ as seen from p₂", which is the note's
invariant I1 (anchor = the class whose view `p₁` is in). See `Cases.lean` for what a
wrong `c₂` computes instead.
-/
theorem compose (p₁ : Ty) (c₁ : Class) (p₂ : Ty) (c₂ : Class) (t : Ty)
    (h : inView W p₁ c₁ t) :
    asf W p₂ c₂ (asf W p₁ c₁ t) = asf W (asf W p₂ c₂ p₁) c₁ t := by
  induction t with
  | this d => exact thisAsSeen_asf W d c₁ p₂ c₂ p₁ (h d (by simp [Ty.thisLeaves]))
  | sel q v ih =>
    simp only [asf]; rw [ih (fun d hd => h d (by simpa [Ty.thisLeaves] using hd))]
  | pair a b iha ihb =>
    simp only [asf]
    rw [iha (fun d hd => h d (by simp [Ty.thisLeaves, hd])),
        ihb (fun d hd => h d (by simp [Ty.thisLeaves, hd]))]
  | tvar n => rfl

/-- A link is a prefix and an anchor. A chain is applied left to right, as
`ScSubstitutor.followed` does. -/
structure Link where
  pre    : Ty
  anchor : Class

def applyChain (links : List Link) (t : Ty) : Ty :=
  links.foldl (fun acc l => asf W l.pre l.anchor acc) t

/-- The single prefix a chain amounts to: the first link's prefix, viewed through all
the later links. -/
def composedPrefix : List Link → Ty → Ty
  | [],      p => p
  | l :: ls, p => composedPrefix ls (asf W l.pre l.anchor p)

/--
**A chain is one `asSeenFrom`.** For any chain whose first link resolves every
this-leaf of the input, applying the whole chain equals one `asSeenFrom` anchored at
the first link's anchor, from the composed prefix. Termination of the chain is
inherited from termination of each walk. This is the "staged evaluation" claim of the
note: the chain architecture is sound in principle.
-/
theorem chain_is_single (l : Link) (ls : List Link) (t : Ty)
    (h : inView W l.pre l.anchor t) :
    applyChain W (l :: ls) t = asf W (composedPrefix W ls l.pre) l.anchor t := by
  induction ls generalizing l with
  | nil => rfl
  | cons l₂ rest ih =>
    simp only [applyChain, List.foldl, composedPrefix] at *
    have step : asf W l₂.pre l₂.anchor (asf W l.pre l.anchor t)
              = asf W (asf W l₂.pre l₂.anchor l.pre) l.anchor t := compose W _ _ _ _ _ h
    rw [step]
    have h' : inView W (asf W l₂.pre l₂.anchor l.pre) l.anchor t := by
      intro d hd; rw [rewrites_asf]; exact h d hd
    exact ih ⟨asf W l₂.pre l₂.anchor l.pre, l.anchor⟩ h'

/-- Idempotence (the "no re-entry" invariant I4): re-running a link on its own output
changes nothing when the link's prefix is fixed by the link, i.e. the prefix mentions
no this-type on the anchor's chain. In IntelliJ, "no self-embedding" is the brake that
stands in for this condition. -/
theorem idempotent (p : Ty) (c : Class) (t : Ty)
    (h : inView W p c t) (hp : asf W p c p = p) :
    asf W p c (asf W p c t) = asf W p c t := by
  rw [compose W p c p c t h, hp]

/-! ## Structural constraints on a chain, as named statements

Three constraints that can be asserted on a chain without knowing the type it will be
applied to. Each is the formal counterpart of a runtime check proposed for
`ScSubstitutor` / `ThisTypeSubstitution`.
-/

section Constraints

-- The class a prefix is an instance of (`target.widen.extractClass`).
variable (viewClass : Ty → Class)

/-- `p` as seen from `q`: scalac's `p.asSeenFrom(q, cls(p))`. -/
def seenFrom (p q : Ty) : Ty := asf W q (viewClass p) p

/-- The prefix a well-formed selection chain *means*: the first prefix, viewed through
each later prefix from the class it is an instance of. -/
def intendedPrefix : List Link → Ty → Ty
  | [],      p => p
  | l :: ls, p => intendedPrefix ls (seenFrom W viewClass p l.pre)

/-- **C1 (anchor = running view).** Starting from the first link's prefix `p`, each later
link is anchored at the class of the prefix composed so far. Checkable in
`ScSubstitutor.followed` by folding the this-links. The cheap form "each anchor is the
class of the previous link's target" is this exactly when the previous link rewrote the
running prefix to its own target, which is the `sig_C >> fromType` shape (the running
prefix is `C.this`, the next target is the `fromType`, and `C.this` seen from it is it). -/
def wellAnchored (p : Ty) : List Link → Prop
  | []      => True
  | l :: ls => l.anchor = viewClass p ∧ wellAnchored (asf W l.pre l.anchor p) ls

omit [Lockstep W] in
theorem composedPrefix_eq_intended (ls : List Link) (p : Ty)
    (h : wellAnchored W viewClass p ls) :
    composedPrefix W ls p = intendedPrefix W viewClass ls p := by
  induction ls generalizing p with
  | nil => rfl
  | cons l rest ih =>
    obtain ⟨ha, hrest⟩ := h
    simp only [composedPrefix, intendedPrefix, seenFrom]
    rw [ha] at hrest ⊢
    exact ih _ hrest

/-- Under C1, a chain is the single `asSeenFrom` from the *intended* prefix, which is
the statement that makes C1 the right assertion: `compose` alone only says the chain is
some single map. -/
theorem chain_is_intended (l : Link) (ls : List Link) (t : Ty)
    (hv : inView W l.pre l.anchor t) (h : wellAnchored W viewClass l.pre ls) :
    applyChain W (l :: ls) t = asf W (intendedPrefix W viewClass ls l.pre) l.anchor t := by
  rw [chain_is_single W l ls t hv, composedPrefix_eq_intended W viewClass ls l.pre h]

/-- **C2 (fixed target).** No this-leaf of the link's own prefix is rewritten by the
link. Checkable at construction, `ScSubstitutor(target, anchor)`: no this-type on
`target`'s spine names a class on `anchor`'s owner chain. -/
def fixedTarget (p : Ty) (c : Class) : Prop :=
  ∀ d ∈ p.thisLeaves, rewrites W d c p = false

omit [Lockstep W] in
theorem thisAsSeen_eq_of_not_rewrites (d c : Class) (p : Ty)
    (h : rewrites W d c p = false) : thisAsSeen W d c p = .this d := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    simp only [thisAsSeen, rewrites] at h ⊢
    by_cases hc : (decide (x :: rest = d) && W.hasBase p (x :: rest)) = true
    · simp [hc] at h
    · simp only [hc] at h ⊢; exact ih _ h

omit [Lockstep W] in
theorem asf_eq_of_fixed (p : Ty) (c : Class) (t : Ty)
    (h : ∀ d ∈ t.thisLeaves, rewrites W d c p = false) : asf W p c t = t := by
  induction t with
  | this d => exact thisAsSeen_eq_of_not_rewrites W d c p (h d (by simp [Ty.thisLeaves]))
  | sel q v ih => simp only [asf]; rw [ih (fun d hd => h d (by simpa [Ty.thisLeaves] using hd))]
  | pair a b iha ihb =>
    simp only [asf]
    rw [iha (fun d hd => h d (by simp [Ty.thisLeaves, hd])),
        ihb (fun d hd => h d (by simp [Ty.thisLeaves, hd]))]
  | tvar n => rfl

/-- C2 makes a link idempotent, hence safe to apply to its own output (the
"no re-entry" invariant I4) … -/
theorem idempotent_of_fixed (p : Ty) (c : Class) (t : Ty)
    (hv : inView W p c t) (hf : fixedTarget W p c) :
    asf W p c (asf W p c t) = asf W p c t :=
  idempotent W p c t hv (asf_eq_of_fixed W p c p hf)

/-- … and a duplicated link in a chain safe to drop (`followed` dedup). -/
theorem dedup (l : Link) (t : Ty) (hv : inView W l.pre l.anchor t)
    (hf : fixedTarget W l.pre l.anchor) :
    applyChain W [l, l] t = applyChain W [l] t := by
  simp only [applyChain, List.foldl]
  exact idempotent_of_fixed W l.pre l.anchor t hv hf

/-- **C3 (threaded state carries no this-links).** A substitutor that is put into
resolve state for *other* references (`matchClauseSubstitutor`) may bind type
variables but must not re-anchor. Modelled as the two kinds of link a substitutor may
hold; a state-safe one has only the first kind. -/
inductive Update where
  | tparam : (Nat → Ty) → Update   -- `TypeParamSubstitution`
  | thisTy : Link → Update         -- `ThisTypeSubstitution`

def substTVars (f : Nat → Ty) : Ty → Ty
  | .this d   => .this d
  | .sel q v  => .sel (substTVars f q) v
  | .pair a b => .pair (substTVars f a) (substTVars f b)
  | .tvar n   => f n

def applyUpdate : Update → Ty → Ty
  | .tparam f, t => substTVars f t
  | .thisTy l, t => asf W l.pre l.anchor t

def applyUpdates (us : List Update) (t : Ty) : Ty := us.foldl (fun acc u => applyUpdate W u acc) t

def stateSafe : List Update → Prop
  | []              => True
  | .tparam _ :: us => stateSafe us
  | .thisTy _ :: _  => False

omit [Lockstep W] in
theorem thisLeaves_substTVars (f : Nat → Ty) (t : Ty) :
    ∀ d ∈ t.thisLeaves, d ∈ (substTVars f t).thisLeaves := by
  induction t with
  | this d => intro d' h; simpa [Ty.thisLeaves, substTVars] using h
  | sel q v ih => intro d h; simp only [Ty.thisLeaves, substTVars] at h ⊢; exact ih d h
  | pair a b iha ihb =>
    intro d h
    simp only [Ty.thisLeaves, substTVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (iha d h)
    · exact Or.inr (ihb d h)
  | tvar n => intro d h; simp [Ty.thisLeaves] at h

omit [Lockstep W] in
/-- A state-safe substitutor never rewrites a this-leaf: every this-type of the input
survives in the output. So threading it into other references' resolution cannot
re-anchor their types, which is what the leak in case (a) did. -/
theorem stateSafe_preserves_this (us : List Update) (hs : stateSafe us) (t : Ty) :
    ∀ d ∈ t.thisLeaves, d ∈ (applyUpdates W us t).thisLeaves := by
  induction us generalizing t with
  | nil => intro d h; simpa [applyUpdates] using h
  | cons u rest ih =>
    cases u with
    | tparam f =>
      intro d h
      simp only [applyUpdates, List.foldl, applyUpdate]
      exact ih hs _ d (thisLeaves_substTVars f t d h)
    | thisTy l => exact absurd hs id

end Constraints

end Chain
