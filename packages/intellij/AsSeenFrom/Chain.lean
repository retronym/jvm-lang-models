import AsSeenFrom.Scalac

/-!
# Chains of links versus one `asSeenFrom`

The plugin types a member with a chain of links `(p₁,c₁) >> (p₂,c₂) >> …`, applied left
to right, each one an anchored walk `asf pᵢ cᵢ`. scalac applies one walk. This file
proves when the chain is one walk, and then which one.

The first half needs no conditions on anchors. `compose` shows that two links make one
link, and `chain_is_single` extends that to a whole chain. The second half names the
conditions a runtime check can assert on a chain without knowing the type it will be
applied to, and proves what each one buys: `wellAnchored` (the chain views from the
intended prefix), `fixedTarget` (a link is idempotent), `stateSafe` (a chain cannot
re-anchor anything).

The one assumption about the world is **lockstep**: an `asSeenFrom` map commutes with
taking a base type's prefix. scalac relies on it (the base types of a mapped type are
the mapped base types); in the plugin it is the contract `BaseTypes.baseType` must meet,
and the TCK's baseType dimension checks it empirically.
-/

namespace Chain
open Scalac

variable (W : World)

/-- Lockstep: an `asSeenFrom` map commutes with `bpre` and preserves `hasBase`. -/
class Lockstep : Prop where
  bpre_comm    : ∀ p₂ c₂ p c, asf W p₂ c₂ (W.bpre p c) = W.bpre (asf W p₂ c₂ p) c
  hasBase_comm : ∀ p₂ c₂ p c, W.hasBase (asf W p₂ c₂ p) c = W.hasBase p c

variable [Lockstep W]

/-- Whether a walk rewrites `D.this` depends only on the prefix's base classes, which
a later map preserves. So a type in a link's view stays in the view of that link with
its prefix mapped. -/
theorem rewrites_asf (d c : Class) (p₂ : Ty) (c₂ : Class) (p : Ty) :
    rewrites W d c (asf W p₂ c₂ p) = rewrites W d c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    simp only [rewrites, Lockstep.hasBase_comm]
    split
    · rfl
    · rw [← Lockstep.bpre_comm]; exact ih _

/-- The key lemma. If the first walk rewrites `D.this`, mapping its result by a second
link is the same as running the first walk over the mapped prefix. The second link
moves the prefix, and lockstep moves the walk's intermediate prefixes with it. -/
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
**Composition law.** Two links in sequence are one link: its prefix is the first link's
prefix as seen by the second link, and its anchor is the first link's anchor.

    asf p₂ c₂ (asf p₁ c₁ t) = asf (asf p₂ c₂ p₁) c₁ t

The hypothesis `inView` says the first link rewrites every this-type of `t`. Without it
the second link would also see this-types the first one left behind, which were written
in some other class's view, and rewrite them from the wrong place. The plugin's check A5
reports a this-type that a link leaves alone where scalac's walk would rewrite it.

The law needs nothing of `c₂`: any second anchor gives *some* single link. The anchor
decides which prefix that link views from, `asf p₂ c₂ p₁`, and so whether it is the
intended one; `chain_is_intended` below is about that, and `Cases.B` shows a wrong `c₂`.
**A mis-anchored chain is still one `asSeenFrom`, from the wrong prefix.**
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

/-- A this-type link, `ThisTypeSubstitution(pre, anchor)`. A chain is a list of links
applied left to right: `applyChain [a, b]` applies `a` first, as `a.followed(b)` does. -/
structure Link where
  pre    : Ty
  anchor : Class

def applyChain (links : List Link) (t : Ty) : Ty :=
  links.foldl (fun acc l => asf W l.pre l.anchor acc) t

/-- The single prefix a chain amounts to: the first link's prefix, viewed through each
later link in turn. -/
def composedPrefix : List Link → Ty → Ty
  | [],      p => p
  | l :: ls, p => composedPrefix ls (asf W l.pre l.anchor p)

/--
**A chain is one `asSeenFrom`.** If the first link rewrites every this-type of `t`,
the whole chain applied to `t` is one walk anchored at the first link's anchor, from the
composed prefix. By `compose`, one link at a time.

This is why one pass suffices. The output of a single walk mentions only pieces of its
prefix, never a this-type the walk was meant to rewrite, so it never needs rewriting
again. The plugin used to refuse results that looked like they did (the
no-self-embedding brake); its check I4 counted those refusals once every link had an
anchor, every sampled one was a rewrite scalac also performs, and the brake was deleted.
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

/-- **Idempotence.** A link that maps its own prefix to itself (`hp`) changes nothing
when applied again to its own output. Without `hp` a link applied twice would view
from its prefix as seen by itself, a different prefix.

The plugin's check A1 tests `hp` directly, by applying the link to its target when the
link is built. -/
theorem idempotent (p : Ty) (c : Class) (t : Ty)
    (h : inView W p c t) (hp : asf W p c p = p) :
    asf W p c (asf W p c t) = asf W p c t := by
  rw [compose W p c p c t h, hp]

/-! ## Conditions a runtime check can assert

`compose` and `chain_is_single` say that a chain is *some* `asSeenFrom`. The conditions
below say *which* one, and each can be checked on the chain alone, where it is built,
without the type it will later be applied to.
-/

section Constraints

-- The class a prefix is an instance of: `target.widen.extractClass` in the plugin.
variable (viewClass : Ty → Class)

/-- `p` as seen from `q`: scalac's `p.asSeenFrom(q, cls(p))`, viewing `p` from the class
it is an instance of. -/
def seenFrom (p q : Ty) : Ty := asf W q (viewClass p) p

/-- The prefix a chain is *meant* to view from: the first prefix, then seen from each
later link's prefix in turn. -/
def intendedPrefix : List Link → Ty → Ty
  | [],      p => p
  | l :: ls, p => intendedPrefix ls (seenFrom W viewClass p l.pre)

/-- **Well anchored.** Starting from the first link's prefix `p`, each later link is
anchored at the class of the prefix composed so far. The plugin's check A4 folds the
this-links of a chain in `followed` to test exactly this; A3 tests the cheap form,
"a link that follows one targeting `Q.this` is anchored at `Q`", which is the same
condition when the running prefix is that `Q.this` itself. -/
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

/-- **A well-anchored chain views from the intended prefix.** This is what makes
`wellAnchored` the right condition to check: `chain_is_single` alone says the chain is
some single `asSeenFrom`, and this says it is the one from `intendedPrefix`.

The plugin's checks A3 and A4 are measurements rather than gates, because the plugin
mostly builds chains of a different shape. `ScalaResolveState.substitutorWithThisType`
prepends the use-site link, so the chain is `use >> sig_C`, the reverse of the
`sig_C >> use` order this condition is stated for; see the README. -/
theorem chain_is_intended (l : Link) (ls : List Link) (t : Ty)
    (hv : inView W l.pre l.anchor t) (h : wellAnchored W viewClass l.pre ls) :
    applyChain W (l :: ls) t = asf W (intendedPrefix W viewClass ls l.pre) l.anchor t := by
  rw [chain_is_single W l ls t hv, composedPrefix_eq_intended W viewClass ls l.pre h]

/-- **Fixed target.** The link rewrites no this-type of its own prefix. A syntactic
condition sufficient for `idempotent`'s `hp` (via `asf_eq_of_fixed`). It is stronger
than needed: `Outer.this.i.type` seen from `Inner` violates it yet maps to itself, which
is why the plugin's A1 checks `hp` directly. -/
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
/-- A link leaves alone a type none of whose this-types it rewrites. -/
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

/-- A link with a fixed target is idempotent. -/
theorem idempotent_of_fixed (p : Ty) (c : Class) (t : Ty)
    (hv : inView W p c t) (hf : fixedTarget W p c) :
    asf W p c (asf W p c t) = asf W p c t :=
  idempotent W p c t hv (asf_eq_of_fixed W p c p hf)

/-- To state the next condition a chain needs both kinds of link: a type-argument
binding and a this-type rewrite. -/
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

/-- **State safe.** A chain stored in resolver state is applied later to the types of
*other* references (`matchClauseSubstitutor`, for the references in a case body). Such a
chain may bind type parameters, which mean the same thing wherever they occur, but must
not hold a this-type rewrite, whose meaning depends on the class its input was written
in. -/
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
/-- **A state-safe chain cannot re-anchor.** Every this-type of the input survives in
the output, so storing the chain in resolver state cannot move another reference's
type into the wrong view. The plugin's check A2 found exactly this leak: the chain for a
`case FlatMap(f, k) =>` pattern, `` `this` -> IO.this.type asSeenFrom FlatMap >> Map(A -> Any, B -> A) ``,
was stored for the whole case body. The body now receives only the type bindings, and
A2 fails the tests if a this-link reaches resolver state again. -/
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
