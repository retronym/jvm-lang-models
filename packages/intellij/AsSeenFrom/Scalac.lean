import AsSeenFrom.Model

/-!
# scalac: `asSeenFrom` as one anchored walk

`thisAsSeen d c p` is `AsSeenFromMap(p, c).thisTypeAsSeen(ThisType(d))`
(`scala/reflect/internal/tpe/TypeMaps.scala`):

    loop(pre, clazz):
      if clazz is a package                      → leave D.this alone
      else if clazz == D && pre baseType clazz exists   (matchesPrefixAndClass)
                                                 → pre
      else loop((pre baseType clazz).prefix, clazz.owner)

The walk is structural recursion on the cursor class, so Lean's termination checker
is the termination proof (property P1/P2 of the note: the cursor is anchored, and
`pre` and the cursor step in lockstep).

`asf p c` is the whole map: it rewrites this-leaves and goes through structure.
`memberType pre m = asf pre (owner m) (info m)`.
-/

namespace Scalac

variable (W : World)

def thisAsSeen (d : Class) : Class → Ty → Ty
  | [],           _ => .this d
  | c@(_ :: rest), p =>
      if c = d && W.hasBase p c then p
      else thisAsSeen d rest (W.bpre p c)

def asf (p : Ty) (c : Class) : Ty → Ty
  | .this d   => thisAsSeen W d c p
  | .sel q v  => .sel (asf p c q) v
  | .pair a b => .pair (asf p c a) (asf p c b)
  | .tvar n   => .tvar n

/-- Does the walk anchored at `c` over `p` rewrite `D.this`? (`matchesPrefixAndClass`
succeeds at some step.) -/
def rewrites (d : Class) : Class → Ty → Bool
  | [],            _ => false
  | c@(_ :: rest), p =>
      if c = d && W.hasBase p c then true
      else rewrites d rest (W.bpre p c)

/-- `T` is fully in the view that `(p, c)` resolves: every this-leaf gets rewritten.
This is the note's "the type is in the view of class `c`", made relative to the
prefix because scalac's match also needs `p baseType c`. -/
def inView (p : Ty) (c : Class) (t : Ty) : Prop :=
  ∀ d ∈ t.thisLeaves, rewrites W d c p = true

/-- P3: the result for a this-leaf is either the leaf itself or some iterated
`bpre` of `p`; it never contains `D.this` by construction. Stated as: the result is
`p` after `k` `bpre` steps, for the cursors walked. -/
theorem thisAsSeen_shape (d : Class) (c : Class) (p : Ty) :
    thisAsSeen W d c p = .this d ∨
    ∃ cs : List Class, thisAsSeen W d c p = cs.foldl W.bpre p := by
  induction c generalizing p with
  | nil => left; rfl
  | cons x rest ih =>
    simp only [thisAsSeen]
    split
    · right; exact ⟨[], rfl⟩
    · rcases ih (W.bpre p (x :: rest)) with h | ⟨cs, h⟩
      · left; exact h
      · right; exact ⟨(x :: rest) :: cs, by simpa using h⟩

end Scalac
