/-!
# MegaPhase fusion: when is one traversal the same as two?

dotc runs a group of miniphases in one tree traversal (`MegaPhase`): at each node, after its
children are done, every miniphase of the group transforms the node in turn. Run one after the
other instead, miniphase `f` would transform the whole tree before `g` saw any of it. The two
schedules see different trees:

* fused, `f` transforms a node whose children `g` has already transformed (a *later* phase's
  output under an *earlier* phase);
* fused, `g` sees only the root of what `f` returned: a subtree that `f` creates is never visited
  by `g` unless `f` asks for it (`transformFollowing`, `transformFollowingDeep`);
* fused, `g` at a node sees ancestors and right siblings that `f` has not reached yet: a
  `prepareFor*` pre-pass sees the group's input, not `f`'s output (the reason for
  `runsAfterGroupsOf`);
* fused, every miniphase runs at the phase after the group's *last* miniphase
  (`atPhase(miniPhases.last.next)`, [scala/scala3#3350](https://github.com/scala/scala3/pull/3350),
  for 6-7% speed), so an early miniphase sees the infos that later ones in its group produce.

This file models the first two with bottom-up transforms over rose trees, proves that fusion is
transparent when the earlier phase only relabels the node it is given, and gives a witness for
each way out of that condition. The first is measured: `packages/scala/probes/phases/Fusion3.scala`
compiles dotty's `tests/run` both ways; in `tests/run/19384.scala`, `ExtensionMethods` positions a
value class's forwarder at its method's right-hand side (`fwd.withSpan(originalDef.rhs.span)`),
and fused, `PatternMatcher`, later in the same group, has already replaced that `match`: the
forwarder's line number differs. The others, measured the same way: `CapturedVars` collects the
mutable locals that closures capture in a pre-pass over its group's input, before `LazyVals` (same
group) makes lazy-val holders `Mutable`, so unfused it boxes the holders in `ObjectRef`s; `Memoize`
reads "no field yet" as "no field needed" and fused only sees Mixin's trait setter after the getter
(`transformFollowing`), so unfused a trait's val initializer is dropped and `tests/run/final-fields`
prints `0` for `-4`; and `DropOuterAccessors`, fused, sees owners after `Flatten`, so it keeps outer
accessors that `CountOuterAccesses` (another group) counted as droppable.
-/

namespace ScalaTypes.Fusion

/-- A tree: a label and children. -/
inductive Tree (α : Type) where
  | node : α → List (Tree α) → Tree α
  deriving Repr

open Tree

/-- A miniphase's node transform: given a node's label and its (already transformed) children. -/
abbrev Mini (α : Type) := α → List (Tree α) → Tree α

mutual
/-- One traversal, bottom up. -/
def post {α} (f : Mini α) : Tree α → Tree α
  | node a cs => f a (postAll f cs)
def postAll {α} (f : Mini α) : List (Tree α) → List (Tree α)
  | [] => []
  | c :: cs => post f c :: postAll f cs
end

theorem postAll_eq_map {α} (f : Mini α) : ∀ cs, postAll f cs = cs.map (post f)
  | [] => rfl
  | c :: cs => by simp [postAll, postAll_eq_map f cs]

/-- Apply a transform at the root only. -/
def atRoot {α} (g : Mini α) : Tree α → Tree α
  | node a cs => g a cs

/-- Sequential: `f` over the whole tree, then `g`. -/
def seq {α} (f g : Mini α) (t : Tree α) : Tree α := post g (post f t)

/-- Fused: at each node, `f` then `g` on what `f` returned. -/
def fused {α} (f g : Mini α) : Tree α → Tree α := post fun a cs => atRoot g (f a cs)

/-- A relabelling: the node's new label depends on its label alone, and the children are kept. -/
def relabel {α} (r : α → α) : Mini α := fun a cs => node (r a) cs

theorem post_node {α} (f : Mini α) (a : α) (cs : List (Tree α)) :
    post f (node a cs) = f a (cs.map (post f)) := by
  rw [post, postAll_eq_map]

/-- **Fusion is transparent when the earlier phase only relabels**, whatever the later phase
does. -/
theorem fused_eq_seq_of_relabel {α} (r : α → α) (g : Mini α) :
    ∀ t, fused (relabel r) g t = seq (relabel r) g t
  | node a cs => by
    have ih : ∀ c ∈ cs, fused (relabel r) g c = seq (relabel r) g c :=
      fun c _ => fused_eq_seq_of_relabel r g c
    simp only [fused, seq] at *
    rw [post_node, post_node, relabel, atRoot, relabel, post_node, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    simpa [Function.comp] using ih c hc

/-! ## Two ways out

Labels are strings. -/

def leaf (s : String) : Tree String := node s []

/-- `g`, the later phase: compiles a `match` into `labeled` (PatternMatcher). -/
def patmat : Mini String := fun a cs => if a = "match" then node "labeled" cs else node a cs

/-- `f`, the earlier phase: replaces a method body by a forwarder positioned where the body was,
recording the body's root (ExtensionMethods' `withSpan(originalDef.rhs.span)`). -/
def extMethods : Mini String := fun a cs =>
  if a = "def" then node "def" [node ("forwarder@" ++ match cs with | node b _ :: _ => b | [] => "") []]
  else node a cs

/-- The earlier phase reads a child that the later one has already rewritten when fused. -/
theorem reads_child :
    fused extMethods patmat (node "def" [node "match" []]) = node "def" [leaf "forwarder@labeled"] ∧
    seq extMethods patmat (node "def" [node "match" []]) = node "def" [leaf "forwarder@match"] :=
  ⟨rfl, rfl⟩

/-- `f` creates a subtree that `g` should rewrite (shaped like ExpandSAMs making an anonymous class
for a partial function literal; the labels are illustrative). -/
def expandSAM : Mini String := fun a cs =>
  if a = "closure" then node "anonClass" [node "match" []] else node a cs

/-- Fused, the later phase never visits what the earlier one created. -/
theorem creates_subtree :
    fused expandSAM patmat (leaf "closure") = node "anonClass" [leaf "match"] ∧
    seq expandSAM patmat (leaf "closure") = node "anonClass" [leaf "labeled"] :=
  ⟨rfl, rfl⟩

/-- dotc's remedy: the creating phase runs the rest of the group over what it made
(`transformFollowingDeep` in ExpandSAMs and LambdaLift; Mixin's `transformFollowing` carries the
comment "needed to make memoize & lazy vals run"). Modelled by `f` applying `post g` to its new
subtree. -/
def expandSAMFollowing : Mini String := fun a cs =>
  if a = "closure" then node "anonClass" [post patmat (node "match" [])] else node a cs

theorem creates_subtree_following :
    fused expandSAMFollowing patmat (leaf "closure") = seq expandSAMFollowing patmat (leaf "closure") :=
  rfl

end ScalaTypes.Fusion
