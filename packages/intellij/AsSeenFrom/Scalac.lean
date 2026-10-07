import AsSeenFrom.Model

/-!
# scalac: `asSeenFrom` as one anchored walk

This is the reference semantics. `thisAsSeen d c p` is
`AsSeenFromMap(p, c).thisTypeAsSeen(D.this)` (`scala/reflect/internal/tpe/TypeMaps.scala`):

    loop(pre, clazz):
      if clazz is a package                              → leave D.this alone
      else if clazz == D && pre baseType clazz exists    → pre   (matchesPrefixAndClass)
      else loop((pre baseType clazz).prefix, clazz.owner)

The cursor `clazz` starts at the anchor and climbs one enclosing class per step, and `pre`
moves to the matching enclosing instance at the same time, so after `k` steps the two
describe the same nesting level. `D.this` is rewritten only when the cursor *is* `D`.
The recursion is on the cursor's list, so Lean's termination checker is the termination
proof.

`asf p c` is the whole map: it applies the walk to every this-type and goes through the
rest of the structure. scalac's member type is `memberType pre m = asf pre (owner m) (info m)`.
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

/-- Does the walk anchored at `c` over `p` rewrite `D.this`, that is, does
`matchesPrefixAndClass` succeed at some step? -/
def rewrites (d : Class) : Class → Ty → Bool
  | [],            _ => false
  | c@(_ :: rest), p =>
      if c = d && W.hasBase p c then true
      else rewrites d rest (W.bpre p c)

/-- `t` is in the view that the link `(p, c)` resolves: the walk rewrites every this-type
in `t`. Informally, `t` was written inside `c`, and every this-type it mentions is one
of `c`'s enclosing classes that `p` actually has an instance of. This is the hypothesis
of `Chain.compose`; a this-type it leaves behind is what the plugin's check A5 looks for. -/
def inView (p : Ty) (c : Class) (t : Ty) : Prop :=
  ∀ d ∈ t.thisLeaves, rewrites W d c p = true

end Scalac
