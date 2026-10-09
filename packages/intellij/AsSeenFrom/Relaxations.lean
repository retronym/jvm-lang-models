import AsSeenFrom.Chain

/-!
# Relaxing A1: which non-idempotent links are still right

The plugin's check A1 looks at each this-link the first time it is used. Applying the
link to its own target must give the target back (`Chain.idempotent`'s `hp`), or the link
must be self-rooted (`Chain.SelfRooted`) and occur at most once in its chain. Over
scala/scala, links of three further shapes fail both arms and are, as far as anyone can
tell, right. A proposed change admits them:

* (a) **compound self-rooted.** The target is a compound with a part rooted in the
  anchor's this-type: `T1.this -> T1 with T1.this.M3`. Admitted once per chain, like a
  self-rooted path. The same change fixes `ScProjectionType.processType`, which applied
  such a link twice and grew `T1 with (T1 with T1.this.M3)#M3`.
* (b) **outer-rooted.** The target is a path rooted in the this-type of a class strictly
  enclosing the anchor: `I2.this -> T2.this.v12.type`, `T2` enclosing `I2`. Admitted
  once per chain.
* (c) **respelled.** Applied to its own target, the link gives the target back up to
  path aliases and the order of a compound's parts: `T0 with a15.I6 with v14.I6` comes
  back as `T0 with k0.I6`, given `val v14: k0.type; val a15: v14.type`. Admitted as fixed.

(a) and (b) lean on `Chain.once_is_scalac`, which assumes nothing of the link, only that
no later link moves its target. This file says what each shape does when it is applied
to its own target, which is what decides whether a second copy is harmful, and closes
two gaps in the informal argument: that "at most one copy" is not the same as "no later
link moves the target" (`once_is_scalac_of_disjoint` gives a checkable condition for the
latter), and that (c) needs `once_is_scalac` up to an equivalence, which only holds for
an equivalence the map respects (`PathEqv`).
-/

namespace Relax
open Scalac Chain

variable (W : World)

/-! ## Facts about one pass -/

/-- A walk that rewrites `D.this` does so at some step of its climb, so `D` is the anchor
or one of its enclosing classes. -/
theorem rewrites_suffix (d c : Class) (p : Ty) (h : rewrites W d c p = true) : d <:+ c := by
  induction c generalizing p with
  | nil => simp [rewrites] at h
  | cons x rest ih =>
    simp only [rewrites] at h
    by_cases hc : (decide (x :: rest = d) && W.hasBase p (x :: rest)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [← hc.1]; exact List.suffix_refl _
    · simp only [hc] at h
      exact (ih _ h).trans (List.suffix_cons x rest)

/-- At the anchor itself the walk matches at its first step, if the prefix is an
instance of the anchor. -/
theorem thisAsSeen_anchor (p : Ty) (c : Class) (hc : c ≠ []) (hb : W.hasBase p c = true) :
    thisAsSeen W c c p = p := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hc
  simp [thisAsSeen, hb]

/-- A path rooted in `D.this`, under any anchor, is that path with its root replaced by
whatever the walk makes of `D.this`. `Chain.asf_rooted` is the case `D = C`. -/
theorem asf_rootedAt (p : Ty) (c d : Class) (q : Ty) (hq : RootedAt d q) :
    asf W p c q = graft (thisAsSeen W d c p) q := by
  induction hq with
  | root => simp [asf, graft]
  | sel v _ ih => simp [asf, graft, ih]

theorem graft_self (d : Class) (q : Ty) (hq : RootedAt d q) : graft (.this d) q = q := by
  induction hq with
  | root => simp [graft]
  | sel v _ ih => simp [graft, ih]

theorem graft_inj (d : Class) (a b q : Ty) (hq : RootedAt d q) (h : graft a q = graft b q) :
    a = b := by
  induction hq with
  | root => simpa [graft] using h
  | sel v _ ih => exact ih (by simpa [graft] using h)

/-- The number of nodes in a type. It replaces `pathDepth` for compounds: replacing a
leaf never shrinks a type, and replacing one by a non-leaf grows it. -/
def size : Ty → Nat
  | .this _   => 1
  | .sel q _  => size q + 1
  | .pair a b => size a + size b + 1
  | .tvar _   => 1

theorem size_pos (t : Ty) : 0 < size t := by
  cases t <;> simp [size]

/-- A link never shrinks a type: it only replaces leaves. -/
theorem size_asf_ge (p : Ty) (c : Class) (t : Ty) : size t ≤ size (asf W p c t) := by
  induction t with
  | this d => simp only [size, asf]; exact size_pos (thisAsSeen W d c p)
  | sel q v ih => simp [size, asf]; omega
  | pair a b iha ihb => simp [size, asf]; omega
  | tvar n => simp [asf]

/-- A link whose target is an instance of the anchor and not a single leaf strictly
grows any type that mentions the anchor's this-type. -/
theorem size_asf_gt (p : Ty) (c : Class) (t : Ty) (hc : c ≠ []) (hb : W.hasBase p c = true)
    (hp : 1 < size p) (hm : c ∈ t.thisLeaves) : size t < size (asf W p c t) := by
  induction t with
  | this d =>
    simp only [Ty.thisLeaves, List.mem_singleton] at hm
    subst hm
    simpa [size, asf, thisAsSeen_anchor W p c hc hb] using hp
  | sel q v ih =>
    simp only [size, asf]; have := ih (by simpa [Ty.thisLeaves] using hm); omega
  | pair a b iha ihb =>
    simp only [Ty.thisLeaves, List.mem_append] at hm
    simp only [size, asf]
    rcases hm with h | h
    · have := iha h; have := size_asf_ge W p c b; omega
    · have := ihb h; have := size_asf_ge W p c a; omega
  | tvar n => simp [Ty.thisLeaves] at hm

/-- **A link that moves its own target is wrong twice.** If the target `p` is an
instance of the anchor and the link moves it, the chain `l >> l` applied to `C.this`
differs from `l` alone, which is scalac's `asf p c`. Every shape below that moves its
target inherits `selfRooted_twice_diverges` through this. -/
theorem twice_diverges_of_moves (l : Link) (hc : l.anchor ≠ [])
    (hb : W.hasBase l.pre l.anchor = true) (hm : asf W l.pre l.anchor l.pre ≠ l.pre) :
    applyChain W [l, l] (.this l.anchor) ≠ applyChain W [l] (.this l.anchor) := by
  have h1 : asf W l.pre l.anchor (.this l.anchor) = l.pre := by
    simp [asf, thisAsSeen_anchor W _ _ hc hb]
  simp only [applyChain, List.foldl, h1]
  exact hm

/-! ## (a) Compound targets with a part rooted in the anchor -/

/-- `PartRootedAt c t`: some part of `t` is a path rooted in `C.this`, where parts are
the operands of compounds and the prefixes of projections. `T1 with T1.this.M3` has the
part `T1.this.M3`; `(T1 with T1.this.M3)#M3` has it too. -/
inductive PartRootedAt (c : Class) : Ty → Prop
  | path {q : Ty} : RootedAt c q → PartRootedAt c q
  | sel {q : Ty} (v : Nat) : PartRootedAt c q → PartRootedAt c (.sel q v)
  | left {a : Ty} (b : Ty) : PartRootedAt c a → PartRootedAt c (.pair a b)
  | right (a : Ty) {b : Ty} : PartRootedAt c b → PartRootedAt c (.pair a b)

theorem rootedAt_mem {c : Class} {q : Ty} (h : RootedAt c q) : c ∈ q.thisLeaves := by
  induction h with
  | root => simp [Ty.thisLeaves]
  | sel v _ ih => simpa [Ty.thisLeaves] using ih

/-- Having a part rooted in `C.this` is the same as mentioning `C.this` at all: every
this-type sits at the root of some path. So the runtime check can test the target's
this-leaves rather than its shape. -/
theorem partRootedAt_iff (c : Class) (t : Ty) : PartRootedAt c t ↔ c ∈ t.thisLeaves := by
  constructor
  · intro h
    induction h with
    | path h => exact rootedAt_mem h
    | sel v _ ih => simpa [Ty.thisLeaves] using ih
    | left b _ ih => simp [Ty.thisLeaves, ih]
    | right a _ ih => simp [Ty.thisLeaves, ih]
  · intro h
    induction t with
    | this d =>
      simp only [Ty.thisLeaves, List.mem_singleton] at h
      subst h; exact .path .root
    | sel q v ih => exact .sel v (ih (by simpa [Ty.thisLeaves] using h))
    | pair a b iha ihb =>
      simp only [Ty.thisLeaves, List.mem_append] at h
      rcases h with h | h
      · exact .left b (iha h)
      · exact .right a (ihb h)
    | tvar n => simp [Ty.thisLeaves] at h

/-- `replThis c p t`: every `C.this` in `t` replaced by `p`, nothing else touched. -/
def replThis (c : Class) (p : Ty) : Ty → Ty
  | .this d   => if d = c then p else .this d
  | .sel q v  => .sel (replThis c p q) v
  | .pair a b => .pair (replThis c p a) (replThis c p b)
  | .tvar n   => .tvar n

/-- **One pass grafts every rooted part.** The compound form of `Chain.asf_rooted`.
A link whose target is an instance of its anchor replaces every `C.this` of its input by
the target, and does not look inside what it put there. The other this-leaves are
walked as usual; where the walk leaves them alone (`hother`), one pass is exactly the
replacement. Without `hother` the statement is the definition of `asf`: each leaf is
mapped independently, and the replaced ones become `p`. -/
theorem asf_partRooted (p : Ty) (c : Class) (t : Ty) (hc : c ≠ []) (hb : W.hasBase p c = true)
    (hother : ∀ d ∈ t.thisLeaves, d ≠ c → rewrites W d c p = false) :
    asf W p c t = replThis c p t := by
  induction t with
  | this d =>
    simp only [asf, replThis]
    by_cases hd : d = c
    · subst hd; simp [thisAsSeen_anchor W p d hc hb]
    · simp only [hd, ↓reduceIte]
      exact thisAsSeen_eq_of_not_rewrites W d c p (hother d (by simp [Ty.thisLeaves]) hd)
  | sel q v ih =>
    simp only [asf, replThis]
    rw [ih (fun d hd => hother d (by simpa [Ty.thisLeaves] using hd))]
  | pair a b iha ihb =>
    simp only [asf, replThis]
    rw [iha (fun d hd => hother d (by simp [Ty.thisLeaves, hd])),
        ihb (fun d hd => hother d (by simp [Ty.thisLeaves, hd]))]
  | tvar n => rfl

/-- **Compound self-rooted.** The link `(p, c)` has a target that is an instance of `c`,
is not `C.this` itself, and has a part rooted in `C.this`. `Chain.SelfRooted` is the
case where the target is a single path (`SelfRooted.partSelfRooted`). -/
structure PartSelfRooted (p : Ty) (c : Class) : Prop where
  nonempty  : c ≠ []
  part      : PartRootedAt c p
  proper    : p ≠ .this c
  instance_ : W.hasBase p c = true

theorem SelfRooted.partSelfRooted {p : Ty} {c : Class} (h : SelfRooted W p c) :
    PartSelfRooted W p c :=
  ⟨h.nonempty, .path h.rooted, h.proper, h.instance_⟩

/-- **A compound self-rooted link does not fix its target.** Applied to its own target
it grafts the target into each rooted part, which makes it strictly bigger. -/
theorem partRooted_moves_target (p : Ty) (c : Class) (h : PartSelfRooted W p c) :
    asf W p c p ≠ p := by
  have hm : c ∈ p.thisLeaves := (partRootedAt_iff c p).1 h.part
  have hp : 1 < size p := by
    cases p with
    | this d =>
      simp only [Ty.thisLeaves, List.mem_singleton] at hm
      exact absurd (by rw [hm]) h.proper
    | sel q v => have := size_pos q; simp [size]; omega
    | pair a b => have := size_pos a; have := size_pos b; simp [size]; omega
    | tvar n => simp [Ty.thisLeaves] at hm
  intro heq
  have := size_asf_gt W p c p h.nonempty h.instance_ hp hm
  rw [heq] at this
  exact Nat.lt_irrefl _ this

/-- **Twice diverges, compound form.** This is the `ScProjectionType.processType`
duplicate: the link `T1.this -> T1 with T1.this.M3`, applied twice to `T1.this`, gives
`T1 with (T1 with T1.this.M3)#M3` where scalac gives `T1 with T1.this.M3` (`Cases.D`). -/
theorem partRooted_twice_diverges (l : Link) (h : PartSelfRooted W l.pre l.anchor) :
    applyChain W [l, l] (.this l.anchor) ≠ applyChain W [l] (.this l.anchor) :=
  twice_diverges_of_moves W l h.nonempty h.instance_ (partRooted_moves_target W _ _ h)

/-- A chain that holds a compound self-rooted link twice falls outside `once_is_scalac`. -/
theorem partRooted_dup_not_fixed (l : Link) (ls : List Link)
    (h : PartSelfRooted W l.pre l.anchor) (hdup : l ∈ ls) :
    ¬ ∀ l' ∈ ls, asf W l'.pre l'.anchor l.pre = l.pre :=
  fun hfix => partRooted_moves_target W _ _ h (hfix l hdup)

/-- **Once is scalac's, compound form.** `once_is_scalac` assumes nothing of the first
link, so it covers relaxation (a) for a part rooted in the anchor as it stands. Restated
here so the plugin's A1 has a theorem to cite for that arm: **a compound self-rooted
link is right once**, and by `partRooted_twice_diverges` wrong twice. The case of a part
rooted in an *inheritor*'s this-type (`T2.this -> T0 with T3.this.type with T3.this.I5`,
`T3 <: T2`) is not covered: scalac's walk leaves `T3.this` alone, so the link is fixed in
the model's scalac, and only the plugin's own handling of inheritors moves it. -/
theorem partRooted_once_is_scalac [Lockstep W] (l : Link) (ls : List Link) (t : Ty)
    (_h : PartSelfRooted W l.pre l.anchor)
    (hv : inView W l.pre l.anchor t)
    (hfix : ∀ l' ∈ ls, asf W l'.pre l'.anchor l.pre = l.pre) :
    applyChain W (l :: ls) t = asf W l.pre l.anchor t :=
  once_is_scalac W l ls t hv hfix

/-! ## (b) Path targets rooted in an enclosing class

`I2.this -> T2.this.v12.type`, where `T2` encloses `I2`: the target is rooted not in the
anchor's this-type but in an outer one. Whether such a link moves its own target depends
on the world, unlike (a): the walk anchored at `I2` reaches `T2.this` one step out, with
the prefix `(v12 baseType I2).prefix`, and rewrites `T2.this` to that. If `v12` is an
`I2` of this very `T2` (the `Outer.this.i.type` from `Inner` of `fixedTarget`'s doc) the
prefix is `T2.this` and the link is fixed, so A1's first arm already admits it. If `v12`
is an `I2` of some other `T2` instance, the link moves its target, and is right once and
wrong twice like a self-rooted link.

"Right" here means equal to the *model's* scalac, which, like the plugin, substitutes the
prefix it reaches directly. Real scalac does that only for a stable prefix; for an
unstable one it captures the prefix in an existential (`captureThis`), which the model
does not have. The TCK's group G compares the plugin against real scalac on those. -/

/-- **Outer-rooted.** The target `p` is a path rooted in `D.this` for a class `D` that
strictly encloses the anchor `c`, and the walk anchored at `c` over `p` does reach
`D.this` (so the link is not a no-op on it). -/
structure OuterRooted (p : Ty) (c d : Class) : Prop where
  proper  : d ≠ c
  rooted  : RootedAt d p
  reaches : rewrites W d c p = true

theorem OuterRooted.suffix {p : Ty} {c d : Class} (h : OuterRooted W p c d) : d <:+ c :=
  rewrites_suffix W d c p h.reaches

/-- **When an outer-rooted link fixes its target.** Exactly when the walk turns `D.this`
into `D.this`: the link grafts what the walk makes of the root onto the target, and
grafting is injective. -/
theorem outerRooted_fixed_iff (p : Ty) (c d : Class) (hp : RootedAt d p) :
    asf W p c p = p ↔ thisAsSeen W d c p = .this d := by
  rw [asf_rootedAt W p c d p hp]
  constructor
  · intro h
    exact graft_inj d _ _ p hp (h.trans (graft_self d p hp).symm)
  · intro h; rw [h, graft_self d p hp]

/-- **The immediate-owner case, as a world condition.** For an anchor `I` whose owner is
`D`, an outer-rooted link fixes its target exactly when `(p baseType I).prefix` is
`D.this`, that is, when the target is an `I` of this very `D`. -/
theorem outerRooted_fixed_iff_owner (p : Ty) (x : Nat) (d : Class)
    (h : OuterRooted W p (x :: d) d) :
    asf W p (x :: d) p = p ↔ W.bpre p (x :: d) = .this d := by
  rw [outerRooted_fixed_iff W p (x :: d) d h.rooted]
  have hne : (x :: d = d) = False := by
    apply propext; constructor
    · intro e; have := congrArg List.length e; simp at this
    · intro f; exact f.elim
  have hr := h.reaches
  simp only [thisAsSeen, rewrites, hne, decide_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte] at hr ⊢
  -- the walk is now at the cursor `d`, over `q = bpre p (x :: d)`
  generalize W.bpre p (x :: d) = q at hr ⊢
  cases d with
  | nil => simp [rewrites] at hr
  | cons y rest =>
    simp only [thisAsSeen, rewrites, decide_true, Bool.true_and] at hr ⊢
    by_cases hb : W.hasBase q (y :: rest) = true
    · simp [hb]
    · exfalso
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hr
      have := (rewrites_suffix W _ _ _ hr).length_le
      simp at this; omega

/-- **An outer-rooted link that moves its target is wrong twice.** -/
theorem outerRooted_twice_diverges (l : Link) (d : Class) (_h : OuterRooted W l.pre l.anchor d)
    (hc : l.anchor ≠ []) (hb : W.hasBase l.pre l.anchor = true)
    (hm : thisAsSeen W d l.anchor l.pre ≠ .this d) :
    applyChain W [l, l] (.this l.anchor) ≠ applyChain W [l] (.this l.anchor) :=
  twice_diverges_of_moves W l hc hb
    (fun e => hm ((outerRooted_fixed_iff W _ _ _ _h.rooted).1 e))

/-- **Once is scalac's, outer-rooted form.** Again `once_is_scalac` as it stands: an
outer-rooted link that occurs once, with no later link moving its target, gives the
model's scalac result. This justifies relaxation (b) against the model's scalac, which
substitutes an unstable prefix directly; real scalac would capture it existentially. -/
theorem outerRooted_once_is_scalac [Lockstep W] (l : Link) (ls : List Link) (t : Ty) (d : Class)
    (_h : OuterRooted W l.pre l.anchor d)
    (hv : inView W l.pre l.anchor t)
    (hfix : ∀ l' ∈ ls, asf W l'.pre l'.anchor l.pre = l.pre) :
    applyChain W (l :: ls) t = asf W l.pre l.anchor t :=
  once_is_scalac W l ls t hv hfix

/-! ## "At most once" versus "no later link moves the target"

A1 counts copies of a link; `once_is_scalac` needs every later link to leave the target
alone. The two differ: a *different* later link can move the target too. The following
is a condition on anchors and this-leaves alone that a runtime check can assert where
the chain is built: no this-type of the target is a later link's anchor or one of its
enclosing classes. -/

/-- A link leaves alone a type none of whose this-types is its anchor or encloses it. -/
theorem asf_eq_of_disjoint (p : Ty) (c : Class) (t : Ty)
    (h : ∀ d ∈ t.thisLeaves, ¬ d <:+ c) : asf W p c t = t :=
  asf_eq_of_fixed W p c t fun d hd => by
    cases hr : rewrites W d c p
    · rfl
    · exact absurd (rewrites_suffix W d c p hr) (h d hd)

/-- **A checkable sufficient condition for `once_is_scalac`.** If no this-type of the
first link's target is the anchor of a later link or encloses it, the chain is the first
link alone, scalac's result. A second copy of the link violates this condition (its
anchor is a this-leaf of a self-rooted target), as does any later link anchored in or
inside a class the target mentions. -/
theorem once_is_scalac_of_disjoint [Lockstep W] (l : Link) (ls : List Link) (t : Ty)
    (hv : inView W l.pre l.anchor t)
    (hd : ∀ l' ∈ ls, ∀ d ∈ l.pre.thisLeaves, ¬ d <:+ l'.anchor) :
    applyChain W (l :: ls) t = asf W l.pre l.anchor t :=
  once_is_scalac W l ls t hv fun l' hl' => asf_eq_of_disjoint W _ _ _ (hd l' hl')

end Relax
