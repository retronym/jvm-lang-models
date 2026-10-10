import AsSeenFrom.Scalac
import AsSeenFrom.Port

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
re-anchor anything). Last, `once_is_scalac` covers links that are not idempotent: a
self-rooted link is scalac's result as long as it occurs once in a chain.

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
  -- the shared theorem (`Shared.lean`), through `Port`: `asf` is the shared map
  haveI := Port.lockstep W Lockstep.bpre_comm Lockstep.hasBase_comm
  simp only [Port.asf_eq]
  exact AsSeenFrom.compose W.shared _ _ _ _ _ ((Port.inView_iff W _ _ _).1 h)

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

The plugin's check A1 tests `hp` directly, by applying the link to its target the first
time the link is used. A link that fails `hp` is not necessarily wrong: a self-rooted
link (`SelfRooted`) never satisfies it, and is right as long as it occurs once in a
chain (`once_is_scalac`). -/
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

/-! ## Self-rooted links: correct once, wrong twice

`idempotent_of_fixed` covers links whose target the link leaves alone. The plugin also
mints links whose target is a path *rooted in the rewritten class itself*, and these
are not idempotent at all. In scala/scala's `Scanners.scala`:

    class UnitScanner … { lazy val parensAnalyzer = new ParensAnalyzer(…) }
    class ParensAnalyzer … extends UnitScanner(…)

Inside `UnitScanner`, `parensAnalyzer.balance(token)` selects a member that
`ParensAnalyzer` inherits from `UnitScanner`, so its type is viewed through the link
`` `this` -> UnitScanner.this.parensAnalyzer.type asSeenFrom UnitScanner ``. Two different
`UnitScanner` instances now share a name. The `UnitScanner.this` in the member's type is
the receiver, to become `parensAnalyzer`; the `UnitScanner.this` inside the target is the
enclosing scanner. scalac's walk replaces the first and never looks inside what it put
in its place, so the second survives and the result is right:
`UnitScanner.this.parensAnalyzer.T`. A second application of the same link cannot tell
the two apart. It rewrites the surviving one too and gives
`UnitScanner.this.parensAnalyzer.parensAnalyzer.T`, which is wrong. (RefChecks'
`class LevelInfo(val outer: LevelInfo)` gives the same shape, `LevelInfo.this.outer`.)

So such a link relies on two things: the engine does not revisit a leaf it has replaced
(true of `asf`, structurally, and of the plugin's `recursiveUpdate`, which hands a
`ReplaceWith` result to the *next* link, never back to the current one), and the link
does not occur again later in the chain. The lemmas below prove that the first is enough
for one occurrence (`once_is_scalac`), and that a second copy always moves the target
(`selfRooted_dup_not_fixed`) and, applied twice in a row, diverges from scalac
(`selfRooted_twice_diverges`). **A self-rooted link is right exactly once.**
-/

/-- `RootedAt c q`: `q` is a path `C.this.v₁.….vₙ` rooted in `C.this`. -/
inductive RootedAt (c : Class) : Ty → Prop
  | root : RootedAt c (.this c)
  | sel {q : Ty} (v : Nat) : RootedAt c q → RootedAt c (.sel q v)

/-- `graft p q`: the path `q` with its root replaced by `p`. -/
def graft (p : Ty) : Ty → Ty
  | .this _  => p
  | .sel q v => .sel (graft p q) v
  | t        => t

/-- How many selections a path has above its root. -/
def pathDepth : Ty → Nat
  | .sel q _ => pathDepth q + 1
  | _        => 0

/-- **Self-rooted.** The link `(p, c)` has a target `p` that is a proper path rooted in
`C.this`, and `p` is an instance of `c` (`parensAnalyzer : ParensAnalyzer <: UnitScanner`),
so the walk rewrites `C.this` at its first step. The plugin detects this shape with
`ThisTypeSubstitution.embedsRewrittenThis`. -/
structure SelfRooted (p : Ty) (c : Class) : Prop where
  nonempty : c ≠ []
  rooted   : RootedAt c p
  proper   : p ≠ .this c
  instance_ : W.hasBase p c = true

omit [Lockstep W] in
/-- **One pass grafts.** A link applied to a path rooted in its anchor's this-type
replaces the root by the target and does not look inside the target. -/
theorem asf_rooted (p : Ty) (c : Class) (q : Ty) (hc : c ≠ []) (hb : W.hasBase p c = true)
    (hq : RootedAt c q) : asf W p c q = graft p q := by
  induction hq with
  | root =>
    obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hc
    simp [asf, thisAsSeen, graft, hb]
  | sel v _ ih => simp [asf, graft, ih]

theorem depth_graft (p : Ty) (c : Class) (q : Ty) (hq : RootedAt c q) :
    pathDepth (graft p q) = pathDepth p + pathDepth q := by
  induction hq with
  | root => simp [graft, pathDepth]
  | sel v _ ih => simp [graft, pathDepth, ih]; omega

omit [Lockstep W] in
/-- **A self-rooted link does not fix its target.** Applied to its own target it grafts
the target onto itself, which is strictly longer. So `idempotent`'s `hp` fails, and
`idempotent_of_fixed` says nothing about these links. -/
theorem selfRooted_moves_target (p : Ty) (c : Class) (h : SelfRooted W p c) :
    asf W p c p ≠ p := by
  rw [asf_rooted W p c p h.nonempty h.instance_ h.rooted]
  intro heq
  have hd := congrArg pathDepth heq
  rw [depth_graft p c p h.rooted] at hd
  have : pathDepth p ≠ 0 := by
    cases h.rooted with
    | root => exact absurd rfl h.proper
    | sel v _ => simp [pathDepth]
  omega

omit [Lockstep W] in
/-- **Twice diverges.** For a self-rooted link `l`, the chain `l >> l` applied to
`C.this` (any member type that mentions the receiver) differs from `l` alone, which is
scalac's `asf p c`. The second copy rewrites the `C.this` that the first copy brought in
with the target. -/
theorem selfRooted_twice_diverges (l : Link) (h : SelfRooted W l.pre l.anchor) :
    applyChain W [l, l] (.this l.anchor) ≠ applyChain W [l] (.this l.anchor) := by
  have h1 : asf W l.pre l.anchor (.this l.anchor) = l.pre :=
    (asf_rooted W _ _ _ h.nonempty h.instance_ .root).trans (by simp [graft])
  simp only [applyChain, List.foldl, h1]
  exact selfRooted_moves_target W _ _ h

omit [Lockstep W] in
theorem composedPrefix_of_fixed (p : Ty) (ls : List Link)
    (h : ∀ l' ∈ ls, asf W l'.pre l'.anchor p = p) : composedPrefix W ls p = p := by
  induction ls with
  | nil => rfl
  | cons l' rest ih =>
    simp only [composedPrefix]
    rw [h l' (by simp)]
    exact ih (fun l'' hl => h l'' (by simp [hl]))

/-- **Once is scalac's.** If no later link of the chain moves the first link's target,
the chain is that link alone: scalac's `asf p c`. This needs nothing of the link itself,
so it covers self-rooted links, which `idempotent_of_fixed` does not. By
`chain_is_single`, whose composed prefix the later links leave unchanged.

For a self-rooted `l` the hypothesis excludes a second copy of `l` among the later
links (`selfRooted_moves_target`). That is the condition the plugin's A1 checks for
these links: **a self-rooted link may occur at most once in a chain.** -/
theorem once_is_scalac (l : Link) (ls : List Link) (t : Ty)
    (hv : inView W l.pre l.anchor t)
    (hfix : ∀ l' ∈ ls, asf W l'.pre l'.anchor l.pre = l.pre) :
    applyChain W (l :: ls) t = asf W l.pre l.anchor t := by
  rw [chain_is_single W l ls t hv, composedPrefix_of_fixed W l.pre ls hfix]

omit [Lockstep W] in
/-- The hypothesis of `once_is_scalac` fails for any chain that holds a self-rooted
link twice. -/
theorem selfRooted_dup_not_fixed (l : Link) (ls : List Link) (h : SelfRooted W l.pre l.anchor)
    (hdup : l ∈ ls) : ¬ ∀ l' ∈ ls, asf W l'.pre l'.anchor l.pre = l.pre :=
  fun hfix => selfRooted_moves_target W _ _ h (hfix l hdup)

end Chain
