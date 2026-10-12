import ScalaTypes.Resolve
/-!
# The walk over headers is the walk over declarations

`Resolve` writes linearization once, over a `Node`, and instantiates it twice: over whole
declarations (`lin`, what lowering and refchecks read) and over headers (`linH`, the granularity a
bridge keys on). Member lookup likewise: `hits` reads every class's members, `firstHitH` asks one
`member` query per class and stops at the first hit.

This file proves the two agree in every environment whose `header` and `member` answers are
projections of its `decl` answers (`Consistent`, which `Program.envIn` is): the same errors, the
same linearization class by class (`lin_fine`), the same first hit (`firstHit_fine`), and so the
same member lookup (`lookupH_eq`). And it proves that the header walk asks only `header` and
`member` queries (`trace_lookupH`), so a consumer that keys on those covers it.
-/

open Query

namespace Scala

variable {α β γ δ : Type}

abbrev Env := (q : Q) → Ans q

/-- Run an `M` computation against an environment. -/
abbrev ex (e : Env) (x : M α) : Except String α := Task.run e x.run

/-- The queries an `M` computation asks. -/
abbrev tq (e : Env) (x : M α) : List Q := Task.trace e x.run

theorem ex_bind (e : Env) (x : M α) (f : α → M β) :
    ex e (x >>= f) = match ex e x with | .ok a => ex e (f a) | .error s => .error s := by
  simp only [ex, ExceptT.run_bind, Task.bind_eq, Task.run_bind]
  cases Task.run e x.run <;> rfl

theorem tq_bind (e : Env) (x : M α) (f : α → M β) :
    tq e (x >>= f) = tq e x ++ match ex e x with | .ok a => tq e (f a) | .error _ => [] := by
  simp only [tq, ex, ExceptT.run_bind, Task.bind_eq, Task.trace_bind]
  cases Task.run e x.run <;> rfl

@[simp] theorem ex_pure (e : Env) (a : α) : ex e (pure a : M α) = .ok a := rfl
@[simp] theorem tq_pure (e : Env) (a : α) : tq e (pure a : M α) = [] := rfl
@[simp] theorem ex_throw (e : Env) (s : String) : ex e (throw s : M α) = .error s := rfl
@[simp] theorem tq_throw (e : Env) (s : String) : tq e (throw s : M α) = [] := rfl

@[simp] theorem ex_askDecl (e : Env) (n : String) (o : Bool) : ex e (askDecl n o) = .ok (e (.decl n o)) := rfl
@[simp] theorem ex_askHeader (e : Env) (n : String) : ex e (askHeader n) = .ok (e (.header n)) := rfl
@[simp] theorem ex_askMember (e : Env) (n m : String) : ex e (askMember n m) = .ok (e (.member n m)) := rfl
@[simp] theorem tq_askHeader (e : Env) (n : String) : tq e (askHeader n) = [.header n] := rfl
@[simp] theorem tq_askMember (e : Env) (n m : String) : tq e (askMember n m) = [.member n m] := rfl

/-! ## Relating two runs -/

/-- Two results agree up to `R`: both fail with the same message, or both return related values. -/
def RelEx (R : α → β → Prop) : Except String α → Except String β → Prop
  | .ok a, .ok b => R a b
  | .error s, .error s' => s = s'
  | _, _ => False

theorem relEx_bind {R : α → β → Prop} {S : γ → δ → Prop} (e : Env) (x₁ : M α) (x₂ : M β)
    (f₁ : α → M γ) (f₂ : β → M δ) (hx : RelEx R (ex e x₁) (ex e x₂))
    (hf : ∀ a b, R a b → RelEx S (ex e (f₁ a)) (ex e (f₂ b))) :
    RelEx S (ex e (x₁ >>= f₁)) (ex e (x₂ >>= f₂)) := by
  rw [ex_bind, ex_bind]
  revert hx
  cases ex e x₁ <;> cases ex e x₂ <;> simp only [RelEx] <;> intro hx
  · exact hx
  · exact hx.elim
  · exact hx.elim
  · exact hf _ _ hx

/-- Lists related pointwise. -/
def RelL (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ RelL R as bs
  | _, _ => False

theorem RelL.map {R : α → β → Prop} {S : γ → δ → Prop} (f : α → γ) (g : β → δ)
    (h : ∀ a b, R a b → S (f a) (g b)) : ∀ l₁ l₂, RelL R l₁ l₂ → RelL S (l₁.map f) (l₂.map g)
  | [], [], _ => trivial
  | _ :: as, _ :: bs, ⟨hab, hl⟩ => ⟨h _ _ hab, RelL.map f g h as bs hl⟩

theorem RelL.filter {R : α → β → Prop} (p : α → Bool) (q : β → Bool)
    (h : ∀ a b, R a b → p a = q b) : ∀ l₁ l₂, RelL R l₁ l₂ → RelL R (l₁.filter p) (l₂.filter q)
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨hab, hl⟩ => by
    simp only [List.filter_cons, h a b hab]
    split
    · exact ⟨hab, RelL.filter p q h as bs hl⟩
    · exact RelL.filter p q h as bs hl

theorem RelL.append {R : α → β → Prop} : ∀ l₁ l₂ m₁ m₂, RelL R l₁ l₂ → RelL R m₁ m₂ →
    RelL R (l₁ ++ m₁) (l₂ ++ m₂)
  | [], [], _, _, _, hm => hm
  | _ :: as, _ :: bs, m₁, m₂, ⟨hab, hl⟩, hm => ⟨hab, RelL.append as bs m₁ m₂ hl hm⟩

theorem RelL.map_eq {R : α → β → Prop} (f : α → γ) (g : β → γ) (h : ∀ a b, R a b → f a = g b) :
    ∀ l₁ l₂, RelL R l₁ l₂ → l₁.map f = l₂.map g
  | [], [], _ => rfl
  | _ :: as, _ :: bs, ⟨hab, hl⟩ => by simp [h _ _ hab, RelL.map_eq f g h as bs hl]

/-! ## Nodes -/

/-- A declaration and a header node are the same class: the header is the declaration's, and the
name the header was fetched by answers `decl` with the declaration. -/
def RelNode (e : Env) (d : Decl) (h : String × Header) : Prop :=
  h.2 = d.header ∧ ∃ v : View, e (.decl h.1 false) = some v ∧ v.decl = d

def RelAnc (e : Env) (a : Anc) (b : (String × Header) × List Ty) : Prop :=
  RelNode e a.1 b.1 ∧ a.2 = b.2

theorem RelNode.name {e : Env} {d : Decl} {h : String × Header} (r : RelNode e d h) :
    d.name = h.2.name := by rw [r.1]; rfl

theorem ex_map (e : Env) (f : α → β) (x : M α) : ex e (f <$> x) = (ex e x).map f := by
  show Task.run e (ExceptT.map f x).run = Except.map f (Task.run e x)
  simp only [ExceptT.map, ExceptT.run_mk, Task.bind_eq, Task.run_bind]
  cases Task.run e x <;> rfl

theorem ex_needView (e : Env) (n : String) :
    ex e (needView n) = match e (.decl n false) with
      | some v => .ok v | none => .error s!"not found: {n}" := by
  simp only [needView, ex_bind, ex_askDecl]
  cases e (.decl n false) <;> rfl

theorem ex_needHeader (e : Env) (n : String) :
    ex e (needHeader n) = match e (.header n) with
      | some h => .ok h | none => .error s!"not found: {n}" := by
  simp only [needHeader, ex_bind, ex_askHeader]
  cases e (.header n) <;> rfl

theorem fetch_rel (e : Env) (hc : Consistent e) (p : String) :
    RelEx (RelNode e) (ex e (Node.decl.fetch p)) (ex e (Node.header.fetch p)) := by
  show RelEx _ (ex e ((·.decl) <$> needView p)) (ex e (do pure (p, ← needHeader p)))
  rw [ex_map, ex_bind, ex_needView, ex_needHeader, hc.1 p]
  cases hv : e (.decl p false) with
  | none => rfl
  | some v => exact ⟨rfl, v, hv, rfl⟩

/-! ## Linearization -/

theorem linMerge_rel (e : Env) (hc : Consistent e) (self : String)
    (rec₁ : Decl → M (List Anc)) (rec₂ : String × Header → M (List ((String × Header) × List Ty)))
    (hrec : ∀ d h, RelNode e d h → RelEx (RelL (RelAnc e)) (ex e (rec₁ d)) (ex e (rec₂ h))) :
    ∀ ps acc₁ acc₂, RelL (RelAnc e) acc₁ acc₂ →
      RelEx (RelL (RelAnc e)) (ex e (linMerge Node.decl self rec₁ acc₁ ps))
        (ex e (linMerge Node.header self rec₂ acc₂ ps))
  | [], _, _, hacc => hacc
  | (p, pa) :: rest, acc₁, acc₂, hacc => by
    simp only [linMerge]
    refine relEx_bind e _ _ _ _ (fetch_rel e hc p) fun d h hdh => ?_
    refine relEx_bind e _ _ _ _ (hrec d h hdh) fun l₁ l₂ hl => ?_
    apply linMerge_rel e hc self rec₁ rec₂ hrec rest
    have hnames : acc₁.map (·.1.name) = acc₂.map (·.1.2.name) :=
      RelL.map_eq _ _ (fun a b r => r.1.name) _ _ hacc
    refine RelL.append _ _ _ _ (RelL.filter _ _ ?_ _ _ (RelL.map _ _ ?_ _ _ hl)) hacc
    · intro a b r
      have : acc₁.any (·.1.name == a.1.name) = acc₂.any (·.1.2.name == b.1.2.name) := by
        have h := congrArg (fun l => l.any (· == b.1.2.name)) hnames
        simp only [List.any_map, Function.comp_def] at h
        rw [r.1.name]; exact h
      simp only [Node.decl, Node.header, this]
    · intro a b r
      refine ⟨r.1, ?_⟩
      simp only [Node.decl, Node.header, hdh.name, r.2]

theorem lin_fine (e : Env) (hc : Consistent e) :
    ∀ k d h, RelNode e d h → RelEx (RelL (RelAnc e)) (ex e (lin k d)) (ex e (linH k h))
  | 0, _, _, _ => rfl
  | k + 1, d, h, r => by
    simp only [lin, linH, linWith]
    have hn : Node.header.name h = Node.decl.name d := r.name.symm
    have hp : Node.header.parents h = Node.decl.parents d := by
      show h.2.parents = d.parents; rw [r.1]; rfl
    rw [hn, hp]
    refine relEx_bind e _ _ _ _
      (linMerge_rel e hc _ (linWith Node.decl k) (linWith Node.header k) (lin_fine e hc k) _ [] []
        trivial) ?_
    intro l₁ l₂ hl
    refine ⟨⟨r, ?_⟩, ?_⟩
    · simp only [Node.decl, Node.header, r.name]; rw [r.1]; rfl
    · exact hl

/-! ## Member lookup -/

theorem firstHitWith_decl (e : Env) (n self : String) : ∀ l : List Anc,
    ex e (firstHitWith Node.decl (fun d n => pure (d.member n)) self n l) =
      .ok (l.filterMap fun (d, a) =>
        ((d.member n).filter fun m => !m.priv || d.name == self).map fun m => ((d, a), m)).head?
  | [] => rfl
  | (d, ts) :: rest => by
    simp only [firstHitWith, ex_bind, ex_pure, List.filterMap_cons, Node.decl]
    cases (d.member n).filter (fun m => !m.priv || d.name == self) with
    | none => exact firstHitWith_decl e n self rest
    | some m => rfl

/-- Over declarations, reading each class's members without a query: `hits`'s head. -/
theorem firstHit_decl (e : Env) (n : String) (l : List Anc) :
    ex e (firstHitIn Node.decl (fun d n => pure (d.member n)) n l) = .ok (hits l n).head? :=
  firstHitWith_decl e n _ l

theorem firstHit_fine (e : Env) (hc : Consistent e) (n : String) (self : String) :
    ∀ l₁ l₂, RelL (RelAnc e) l₁ l₂ →
      RelEx (fun (a : Option Hit) b => a.map (fun ((d, ts), m) => (d.name, ts, m)) =
          b.map (fun ((h, ts), m) => (h.2.name, ts, m)))
        (ex e (firstHitWith Node.decl (fun d n => pure (d.member n)) self n l₁))
        (ex e (firstHitWith Node.header (fun h n => askMember h.1 n) self n l₂))
  | [], [], _ => rfl
  | (d, ts) :: rest₁, (h, us) :: rest₂, ⟨r, hl⟩ => by
    obtain ⟨⟨hh, v, hv, hvd⟩, hts⟩ := r
    simp only at hh hv hvd hts
    have hm : e (.member h.1 n) = d.member n := by rw [hc.2, hv, Option.bind_some, hvd]
    have hname : Node.decl.name d = Node.header.name h := RelNode.name ⟨hh, v, hv, hvd⟩
    simp only [firstHitWith, ex_bind, ex_pure, ex_askMember, hm, hname]
    split
    · show some (d.name, ts, _) = some (h.2.name, us, _)
      rw [RelNode.name ⟨hh, v, hv, hvd⟩, hts]
    · exact firstHit_fine e hc n self rest₁ rest₂ hl

/-- Member lookup over declarations: the first member named `n` along `c`'s linearization, viewed
from `c`. What `Members` and the embeddings of the toy languages read. -/
def lookup (fuel : Nat) (c n : String) : M (Option Ty) := do
  let d ← need c
  let l ← lin fuel d
  pure (((hits l n).head?).map fun ((o, _), mem) => seenFrom c l o.name mem.res)

theorem RelEx.eq {x y : Except String α} (h : RelEx (· = ·) x y) : x = y := by
  revert h; cases x <;> cases y <;> simp only [RelEx] <;> intro h <;> first | exact h.elim | rw [h]

/-- The names and type arguments of related linearizations. -/
theorem RelL.names {e : Env} {l₁ : List Anc} {l₂ : List ((String × Header) × List Ty)}
    (hl : RelL (RelAnc e) l₁ l₂) :
    l₁.map (fun (a, ts) => (a.name, ts)) = l₂.map (fun (h, ts) => (h.2.name, ts)) :=
  RelL.map_eq _ _ (fun a b r => by
    obtain ⟨⟨d, ts⟩, ⟨h, us⟩⟩ := (a, b)
    show (a.1.name, a.2) = (b.1.2.name, b.2); rw [r.1.name, r.2]) _ _ hl

/-- **The header walk is the declaration walk.** In a consistent environment, member lookup over
headers and `member` queries gives what lookup over whole declarations gives, error or result. -/
theorem lookupH_eq (e : Env) (hc : Consistent e) (fuel : Nat) (c n : String) :
    ex e (lookupH fuel c n) = ex e (lookup fuel c n) := by
  refine (RelEx.eq ?_).symm
  refine relEx_bind e (Node.decl.fetch c) (Node.header.fetch c) _ _ (fetch_rel e hc c) ?_
  intro d h r
  refine relEx_bind e _ _ _ _ (lin_fine e hc fuel d h r) ?_
  intro l₁ l₂ hl
  have hn := hl.names
  have hs : (l₁.head?.map (·.1.name)).getD "" = (l₂.head?.map (Node.header.name ·.1)).getD "" := by
    have := congrArg (fun l => (l.head?.map (·.1)).getD "") hn
    simpa [List.head?_map, Option.map_map, Function.comp_def, Node.header] using this
  have hf := firstHit_fine e hc n ((l₂.head?.map (Node.header.name ·.1)).getD "") l₁ l₂ hl
  rw [firstHitWith_decl] at hf
  have hhits : hits l₁ n = l₁.filterMap fun (d, a) =>
      ((d.member n).filter fun m => !m.priv || d.name == (l₂.head?.map (Node.header.name ·.1)).getD "").map
        fun m => ((d, a), m) := by
    unfold hits; rw [hs]; rfl
  simp only [ex_bind, ex_pure]
  unfold firstHitH firstHitIn
  revert hf
  cases ex e (firstHitWith Node.header (fun h n => askMember h.1 n)
    ((l₂.head?.map (Node.header.name ·.1)).getD "") n l₂) with
  | error s => intro hf; exact hf.elim
  | ok b =>
    intro hf
    simp only [RelEx] at hf
    rw [← hhits] at hf
    cases hh : (hits l₁ n).head? with
    | none =>
      rw [hh] at hf
      cases b with
      | none => rfl
      | some _ => simp at hf
    | some x =>
      rw [hh] at hf
      cases b with
      | none => simp at hf
      | some y =>
        obtain ⟨⟨d', ts'⟩, m'⟩ := x
        obtain ⟨⟨⟨q, h'⟩, us'⟩, m''⟩ := y
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨hname, -, hm⟩ := hf
        show some (seenFrom c l₁ d'.name m'.res) =
          some (seenFromN c (l₂.map fun (h, ts) => (h.2.name, ts)) h'.name m''.res)
        rw [seenFrom, hn, hname, hm]

/-! ## What the header walk asks -/

/-- A query the header walk asks. -/
def Walky : Q → Prop
  | .header _ => True
  | .member .. => True
  | .decl .. => False

/-- Every query of `x` satisfies `P`. -/
def Asks (e : Env) (P : Q → Prop) (x : M α) : Prop := ∀ q ∈ tq e x, P q

theorem Asks.bind {e : Env} {P : Q → Prop} {x : M α} {f : α → M β} (hx : Asks e P x)
    (hf : ∀ a, Asks e P (f a)) : Asks e P (x >>= f) := by
  intro q hq
  rw [tq_bind, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hx q hq
  · revert hq; cases ex e x with
    | ok a => exact hf a q
    | error _ => simp

theorem Asks.pure {e : Env} {P : Q → Prop} (a : α) : Asks e P (Pure.pure a : M α) := by
  intro q hq; simp at hq

theorem Asks.throw {e : Env} {P : Q → Prop} (s : String) : Asks e P (throw s : M α) := by
  intro q hq; simp at hq

/-- A query the header walk's linearization asks: only `header`. -/
def Heady : Q → Prop
  | .header _ => True
  | _ => False

section AsksHeader
variable {P : Q → Prop} (hP : ∀ n, P (.header n))
include hP

theorem asks_fetchH_of (e : Env) (p : String) : Asks e P (Node.header.fetch p) := by
  show Asks e P (do Pure.pure (p, ← needHeader p))
  refine Asks.bind (Asks.bind ?_ fun o => ?_) fun _ => Asks.pure _
  · intro q hq; simp only [tq_askHeader, List.mem_singleton] at hq; subst hq; exact hP p
  · cases o
    · exact Asks.throw _
    · exact Asks.pure _

theorem asks_linMerge_of (e : Env) (self : String)
    (rec : String × Header → M (List ((String × Header) × List Ty)))
    (hrec : ∀ h, Asks e P (rec h)) :
    ∀ ps acc, Asks e P (linMerge Node.header self rec acc ps)
  | [], _ => Asks.pure _
  | (p, _) :: rest, _ => by
    simp only [linMerge]
    exact Asks.bind (asks_fetchH_of hP e p) fun h => Asks.bind (hrec h) fun _ =>
      asks_linMerge_of e self rec hrec rest _

/-- Linearization over headers asks only `header` queries. -/
theorem asks_linH_of (e : Env) : ∀ k h, Asks e P (linH k h)
  | 0, _ => Asks.throw _
  | k + 1, h => by
    simp only [linH, linWith]
    exact Asks.bind (asks_linMerge_of hP e _ _ (asks_linH_of e k) _ []) fun _ => Asks.pure _

end AsksHeader

theorem asks_fetchH (e : Env) (p : String) : Asks e Walky (Node.header.fetch p) :=
  asks_fetchH_of (fun _ => trivial) e p

theorem asks_linH (e : Env) : ∀ k h, Asks e Walky (linH k h) := asks_linH_of (fun _ => trivial) e

theorem asks_firstHitH (e : Env) (n self : String) :
    ∀ l, Asks e Walky (firstHitWith Node.header (fun h n => askMember h.1 n) self n l)
  | [] => Asks.pure _
  | (h, _) :: rest => by
    simp only [firstHitWith]
    refine Asks.bind ?_ fun o => ?_
    · intro q hq; simp only [tq_askMember, List.mem_singleton] at hq; subst hq; trivial
    · split
      · exact Asks.pure _
      · exact asks_firstHitH e n self rest

/-- The header walk asks only `header` and `member` queries. -/
theorem asks_lookupH (e : Env) (fuel : Nat) (c n : String) : Asks e Walky (lookupH fuel c n) := by
  unfold lookupH
  refine Asks.bind (asks_fetchH e c) fun h => Asks.bind (asks_linH e fuel h) fun l =>
    Asks.bind (asks_firstHitH e n _ l) fun o => ?_
  split
  · exact Asks.pure _
  · exact Asks.pure _

end Scala
