import ScalaTypes.Resolve
import ScalaTypes.Desugar
/-!
# Membership and overriding: Scala's refchecks, as a `Task`

For a class `C` the verdict is either the errors scalac (or dotc) reports for `C`, or, per
signature, the member a selection on `C` runs. It is computed over `C`'s interfaces only (`lin`,
`sigGroups`, `memberType` from `Lower` and `AsSeenFrom`), so it is a `Task` like lowering.

The checks are `RefChecks.checkAllOverrides`, per *overriding pair* `(member, other)`, in the order
the compilers' `OverridingPairs.Cursor` forms them (`pairs2`): a signature group's concrete members
first, then its deferred ones, each in linearization order; each member not yet seen as the upper
member of a pair is the lower member of a pair with every later member of another class, which is
then seen. A pair's checks are `checkOverride`'s, in its order (`checkPair`): access, `final`, a
missing `override`, accidental override, `def` over `val`, lazy against strict, result type. A
private member of another class is in no pair (scalac); dotc leaves every private member out, and
reports a private member of the class that matches an inherited one on its own. A pair a parent
already has is left to it in 2.12, checked again in 2.13, and checked again in dotc unless the
parent has the owners in the same order (`handledByParent`). Per class: `override` that overrides
nothing; an abstract member left in a concrete class (`missingS2`, and dotc's own member,
`concreteS3`); dotc's re-check of a member its direct parents give it (`checkMemberTypesOK`).

Errors are reported once per position: an error of a pair whose lower member the class declares is
at that member, every other one at the class, where only the first is reported. Typer's
inheritance checks (a `final` parent, two instances of a base class) come before refchecks and stop
it (`typerDecl`, `reported`).

The member a selection runs is the group's first concrete member along the linearization
(`Lower.winner`): a concrete member is never overridden by an abstract one.

**Against the specification.** SLS §5.1.4 states restrictions on a member and the member it
overrides, and §5.1.3 which member overrides which ("a concrete definition always overrides an
abstract definition"); neither says which errors a compiler prints. Of the rules above, the cursor's
order, the first error per position, the abstract-superclass chain (`missingS2`), dotc's separate
private check and its member-type re-check decide which classes of a rejected program report which
errors, never whether a program compiles: over `membersSpace` and `FlatRules`' 192,000 programs,
scalac 2.12, 2.13 and dotc 3.9 accept the same programs except in two families, both where an
abstract declaration meets a concrete member, which §5.1.3 says it does not override. dotc lets a
trait's abstract declaration re-abstract (`reabsTraitOnly`), and checks an abstract declaration, a
class's or a trait's, as an override of the concrete member (`abstractOverFinal`, and stability:
dotc's `checkAll`, scala/scala3 neg/i11130); scalac does neither and follows the text. Both
compilers let a class's abstract declaration re-abstract, which the text does not (`reabsClass`).
2.12's leaving a pair to a parent is unsound (`recheck11136`). The drafts in `docs/upstream` report
these.

`membersSpace` and `FlatRules`' space (`lake exe scalaprobe OUT flat`) are the calibration spaces;
`packages/scala/probes/members.py` compares the verdicts with scalac 2.12, 2.13 and dotc 3,
including the programs they reject.
-/

open Query

namespace Scala.Members

inductive Kind
  | needsOverride
  | conflicting
  | accidental
  | overridesNothing
  | finalOverride
  | needsAbstract
  | stable
  | lazyMismatch
  | weakerAccess
  | illegalModifiers
  | resultType
  | finalParent
  | baseTypes
  deriving DecidableEq, Repr

def Kind.name : Kind → String
  | .needsOverride => "needsOverride" | .conflicting => "conflicting"
  | .overridesNothing => "overridesNothing" | .finalOverride => "finalOverride"
  | .accidental => "accidental" | .needsAbstract => "needsAbstract" | .stable => "stable"
  | .lazyMismatch => "lazyMismatch" | .weakerAccess => "weakerAccess"
  | .illegalModifiers => "illegalModifiers" | .resultType => "resultType"
  | .finalParent => "finalParent" | .baseTypes => "baseTypes"

/-- An error is reported for a class (or object, or trait). -/
structure Err where
  cls : String
  kind : Kind
  deriving DecidableEq, Repr

/-- The compiler stops before refchecks when an earlier phase reported an error. -/
def Kind.phase : Kind → Nat
  | .illegalModifiers | .finalParent | .baseTypes => 0
  | _ => 1

def isBase (l : List Anc) (a : String) : Bool := l.any (·.1.name == a)

/-- Does a member carry `override`? Explicitly, or as printed: iff it overrides something in its
own class's linearization.

Spec: cites SLS §5.1.4, SLS §5.2 -/
def hasOverride (owner : Decl) (m : Mem) : M Bool := do
  match m.ov with
  | some b => pure b
  | none =>
    let lo ← lin fuel owner
    match lo.head? with
    | some a => pure ((hitsAbove lo m.name).any (overridesIn owner.name lo (a, m)))
    | none => pure false

/-- `t <: u` for the types the spaces use: equal, or a reference type below `Object`.

Spec: cites SLS §3.5.2 -/
def conforms (t u : Ty) : Bool :=
  t == u || (u == .obj && match t with | .int | .bool | .unit => false | _ => true)

/-- The member of a signature group that a selection on the class runs: the first concrete,
non-private one, unless an abstract member of a subclass of its owner comes earlier (the subclass
re-abstracts it). Only a class re-abstracts; an abstract member of a trait does not. `none` when the group has no such member: the class's member is abstract.

Spec: cites SLS §5.1.2, SLS §5.1.3, SLS §5.1.4
Spec: contradicts SLS §5.1.4 / scalac 2.12.21, 2.13.18, dotc 3.9.0: "a concrete definition always
overrides an abstract one", but a class's abstract declaration re-abstracts an inherited concrete
member in both compilers, even with the concrete trait mixed in directly
(`Members.reabsAbstractClass`, `Members.reabsClassDirect`; draft
[spec-reabstraction.md](../../../docs/upstream/spec-reabstraction.md)). -/
def effWinner (self : String) (g : List Hit) : M (Option Hit) := do
  let mut seen : List Hit := []
  for h in g do
    if h.2.priv && h.1.1.name != self then continue
    if !h.2.abs && !h.2.priv then
      let mut reabs := false
      for x in seen do
        if x.2.abs && x.1.1.kind != .trt && isBase (← lin fuel x.1.1) h.1.1.name then reabs := true
      if !reabs then return some h
    seen := seen ++ [h]
  pure none

/-- Scala 3: is member `n` of `d` concrete? dotc computes a class's member from its own
declaration, else from the members of its direct parents, and a parent's member is concrete if any
of them is. So a trait's abstract declaration re-abstracts a concrete member of its own parent,
unless the class also has that parent directly (`class B extends A`, with
`trait A extends M { def m: String }` and a concrete `M.m`, needs to be abstract;
`class B extends M with A` does not). A class's abstract declaration re-abstracts either way
(`effWinner`), in both compilers.

Neither is in the specification, which says a concrete definition always overrides an abstract
one (SLS §5.1.4, and the Scala 3 spec's copy of it): by the text, all of these compile. Scala 2
follows it for traits (and emits a mixin forwarder to the concrete member); javac, by contrast,
always lets an abstract redeclaration win (JLS §9.4.1, §8.4.8), as JVM selection does.

Spec: contradicts SLS §5.1.4 / dotc 3.9.0: a trait's abstract declaration re-abstracts a concrete
member of its own parent unless a direct parent supplies it (`Members.reabsTraitOnly`,
`Members.reabsTraitDirect`, `Members.reabsTraitViaClass`; draft
[dotc-reabstraction-direct-parent.md](../../../docs/upstream/dotc-reabstraction-direct-parent.md)). -/
def concreteS3 (n : String) : Nat → Decl → M Bool
  | 0, _ => pure false
  | k + 1, d => do
    -- a private member is not inherited, and does not implement (`isImplemented` reads
    -- `nonPrivateMembersNamed`)
    match d.members.find? fun mm => mm.name == n && !mm.fieldOnly && !mm.priv with
    | some mm => pure (!mm.abs)
    | none =>
      let mut r := false
      for (p, _) in d.parents do
        if ← concreteS3 n k (← need p) then r := true
      pure r

/-- Does `d`, or a parent reached through abstract classes and traits only, declare `n`? The names
dotc's `checkMemberTypesOK` checks in a concrete class (a concrete parent was checked itself).

Spec: unspecified SLS §5.1.4: which members of a concrete class are checked against what it
inherits. dotc's `RefChecks.checkMemberTypesOK` checks the names declared in the class or in a
parent reached through abstract classes and traits only (a concrete parent was checked itself);
calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 on `Members.membersSpace` and `FlatRules`'
192,000 configurations by `packages/scala/probes/members.py`. -/
def declaredUpAbstract (n : String) : Nat → Decl → M Bool
  | 0, _ => pure false
  | k + 1, d => do
    if d.members.any (·.name == n) then return true
    for (p, _) in d.parents do
      let pd ← need p
      if (pd.kind == .trt || pd.abs) && (← declaredUpAbstract n k pd) then return true
    pure false

/-- `d` and its superclasses as far as they are abstract classes: where Scala 2 looks for deferred
declarations a concrete class must implement (`RefChecks.checkNoAbstractDecls` follows
`superClass` while it is `ABSTRACT`; a trait is never a superclass).

Spec: unspecified SLS §5.2: where a compiler looks for the deferred declarations a concrete class
must implement. scalac's `RefChecks.checkNoAbstractDecls` follows the superclass while it is
abstract; calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 on `Members.membersSpace` and
`FlatRules`' 192,000 configurations by `packages/scala/probes/members.py`. -/
def abstractChain : Nat → Decl → M (List Decl)
  | 0, d => pure [d]
  | k + 1, d => do
    match d.super with
    | some (p, _) =>
      let pd ← need p
      if pd.kind == .cls && pd.abs then pure (d :: (← abstractChain k pd)) else pure [d]
    | none => pure [d]

/-- Scala 2: does concrete class `d` leave the signature group `g` unimplemented? Either no member
of `g` is concrete (`checkNoAbstractMembers`), or a deferred declaration of `d` or of an abstract
superclass in a row (`abstractChain`) re-abstracts the member that implements it: the first concrete
member along the linearization comes from a base class of the declaring class
(`checkNoAbstractDecls`). A concrete class's re-abstraction therefore does not reach its
subclasses: `object X extends C`, with `C` re-abstracting a trait's concrete `m`, compiles.

Spec: cites SLS §5.1.4, SLS §5.2 -/
def missingS2 (d : Decl) (g : List Hit) : M Bool := do
  match g.find? fun h => !h.2.abs && !h.2.priv with
  | none => pure (g.any fun h => h.2.abs && !h.2.priv)
  | some impl =>
    let mut r := false
    for bc in ← abstractChain fuel d do
      if g.any (fun h => h.1.1.name == bc.name && h.2.abs) && isBase (← lin fuel bc) impl.1.1.name then r := true
    pure r

/-- `checkOverride`'s checks of one pair, `member` over `other`, in its order: access, `final`, a
missing `override` (an inherited `override` that overrides nothing in its own class counts as
missing), accidental override (no third member overridden by both), `def` over `val`, lazy against
strict, result type. `None` when the pair is legal.

Spec: cites SLS §5.1.4, SLS §5.2 -/
def checkPair (d : Decl) (l : List Anc) (g : List Hit) (mh oh : Hit) (allowPrivOvr : Bool) : M (Option Kind) := do
  let mo := mh.1.1
  let m := mh.2
  let oo := oh.1.1
  let o := oh.2
  let lmo ← lin fuel mo
  let loo ← lin fuel oo
  let ov ← hasOverride mo m
  let overridesInOwner := (hitsAbove lmo m.name).any (overridesIn mo.name lmo ((mo, []), m))
  let third := g.any fun x => x.1.1.name != mo.name && x.1.1.name != oo.name &&
    isBase lmo x.1.1.name && isBase loo x.1.1.name
  let both := !o.abs && !m.abs
  pure <|
    if m.priv && !allowPrivOvr then some .weakerAccess
    else if o.final then some .finalOverride
    else if both && !(ov && (mo.name == d.name || overridesInOwner)) then
      some (if mo.name == d.name then .needsOverride else .conflicting)
    -- an inherited `override` of a member `other`'s owner does not have, with no third
    -- member overridden by both
    else if both && !isBase lmo oo.name && !third then some .accidental
    else if o.isVal && !m.isVal then some .stable
    else if o.isVal && m.isVal && !o.abs && o.lzy != m.lzy then some .lazyMismatch
    else if !conforms (seenFrom d.name l mo.name m.res) (seenFrom d.name l oo.name o.res) then
      some .resultType
    else none

/-- Is the pair of members of `lo` and `hi` (the lower member's owner first) left to a direct parent
whose linearization is `pl`? 2.12: when the parent has both owners as base classes
(`hasCommonParentAsSubclass`); 2.13 never; dotc also needs them in that order in the parent's
linearization (`canBeHandledByParent`), so a deferred member of a subclass and the concrete member
it re-abstracts are checked again.

Spec: unspecified SLS §5.1.4: whether a subclass checks again an overriding pair a parent already
checked. 2.12 leaves it to the parent, 2.13 checks every pair again, dotc when the parent has the
owners in the other order. 2.12's rule is unsound: `Members.recheck11136` compiles and its JVM
rejects it at load
([mixin-final-override-recheck.md](../../../docs/upstream/mixin-final-override-recheck.md)). -/
def handledByParent (dl : Dialect) (pls : List (List Anc)) (lo hi : String) : Bool :=
  match dl with
  | .s212 => pls.any fun pl => isBase pl lo && isBase pl hi
  | .s213 => false
  | .s3 => pls.any fun pl => isBase pl lo && isBase pl hi &&
      (pl.findIdx? (·.1.name == lo)).getD 0 < (pl.findIdx? (·.1.name == hi)).getD 0

/-- Scala 2's overriding pairs of a signature group, in `OverridingPairs.Cursor`'s order, and their
errors. The cursor's scope holds the group's members but other classes' private ones, the concrete
ones first and then the deferred ones, each in linearization order; each member not yet seen as the
upper member of a pair is the lower member of a pair with every later one of another class that is
not private, which is then seen. So a concrete member pairs with a deferred member of a subclass
that re-abstracts it, the concrete one as the lower member. 2.12 skips a pair when a direct parent
has both owners as base classes (`hasCommonParentAsSubclass`); 2.13 does not. Returns the errors at
lower members `d` declares (the first per member: one message per position) and those of inherited
pairs, in order (`mixinOverrideErrors`).

Spec: cites SLS §5.1.4
Spec: unspecified SLS §5.1.4: which overriding pairs are checked, and which error is reported when a
member breaks several rules. scalac follows `OverridingPairs.Cursor`'s order and reports one error
per position; 2.12 leaves a pair to a parent that has both owners; dotc adds `checkAll`'s check of
each deferred declaration; calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 on
`Members.membersSpace` and `FlatRules`' 192,000 configurations by
`packages/scala/probes/members.py`. -/
def pairs2 (dl : Dialect) (d : Decl) (l : List Anc) (pls : List (List Anc)) (g : List Hit) :
    M (List Kind × List Kind) := do
  -- dotc leaves every private member out (`memberCanMatchInheritedSymbols`); a private member of
  -- `d` that matches an inherited one is reported on its own ("weaker access")
  let cand := g.filter fun h => !(h.2.priv && (dl == .s3 || h.1.1.name != d.name))
  let order := cand.filter (!·.2.abs) ++ cand.filter (·.2.abs)
  let mut seen : List Nat := []
  let mut own : List Kind := []
  if dl == .s3 && g.any (fun h => h.1.1.name == d.name && h.2.priv && h.2.ov != some true) &&
      g.any (fun h => h.1.1.name != d.name && !h.2.priv) then
    own := own ++ [.weakerAccess]
  let mut mixin : List Kind := []
  for (lo, i) in order.zipIdx do
    if seen.contains i then continue
    let mut ownFound := false
    for (hi, j) in order.zipIdx.drop (i + 1) do
      if hi.1.1.name == lo.1.1.name || hi.2.priv then continue
      seen := j :: seen
      if handledByParent dl pls lo.1.1.name hi.1.1.name then continue
      if let some k ← checkPair d l g lo hi (dl == .s3 && lo.2.ov == some true) then
        if lo.1.1.name == d.name then
          if !ownFound then own := own ++ [k]; ownFound := true
        else mixin := mixin ++ [k]
  -- dotc's `checkAll` then checks each deferred declaration of the class against the concrete
  -- members it overrides
  if dl == .s3 then
    for dh in g do
      if dh.1.1.name != d.name || !dh.2.abs then continue
      if own.length > 0 then break
      for oh in g do
        if oh.1.1.name == d.name || oh.2.abs || oh.2.priv then continue
        if let some k ← checkPair d l g dh oh (dh.2.ov == some true) then
          own := own ++ [k]
          break
  pure (own, mixin)

/-- The refchecks errors of definition `d` (a class, trait or object).

Spec: cites SLS §5.1.4, SLS §5.2
Spec: unspecified SLS §5.1.4: which errors refchecks reports for a member, and in which order. Both
compilers report one per member, in the order access, `final`, missing `override`, accidental
override, `def` over `val`, lazy against strict, result type (`Members.checkPair`); calibrated on
the 4,704 programs of `Members.membersSpace` by `packages/scala/probes/members.py` and on
`FlatRules`' 192,000. -/
def checkDecl (dl : Dialect) (d : Decl) : M (List Err) := do
  let l ← lin fuel d
  let pls ← d.parents.mapM fun (p, _) => do lin fuel (← need p)
  let mut ks : List Kind := []
  -- Both compilers report an error once per position. An error of a pair whose lower member `d`
  -- declares is at that member; any other (an inherited pair, an implementation, an abstract member
  -- left) is at the class, so only the first of those is reported (scalac's
  -- `printMixinOverrideErrors`, then the reporter's one message per position).
  let mut atClass := false
  -- Scala 3 rejects `override private` before refchecks
  if dl == .s3 && d.members.any (fun m => m.priv && m.ov == some true) then
    ks := ks ++ [.illegalModifiers]
  for g in sigGroups d.name l do
    -- `override` that overrides nothing
    for h in g do
      if h.1.1.name == d.name && h.2.ov == some true && g.length == 1 then
        ks := ks ++ [.overridesNothing]
    -- the overriding pairs, in the compiler's cursor order (`pairs2`)
    let (own, mixin) ← pairs2 dl d l pls g
    ks := ks ++ own
    if let some k := mixin.head? then
      if !atClass then
        ks := ks ++ [k]
        atClass := true
  -- an abstract member left in a concrete class
  if d.kind != .trt && !d.abs then
    for g in sigGroups d.name l do
      if g.any (fun h => h.2.abs && !h.2.priv) then
        -- both compilers: no concrete member, or a deferred declaration of `d` or of an abstract
        -- superclass in a row re-abstracts the one there is (`missingS2`); Scala 3 also: the
        -- member dotc computes for `d` is abstract, as when a trait re-abstracts and no direct
        -- parent supplies the concrete member (`concreteS3`)
        let byClass ← missingS2 d g
        let byTrait ← if dl == .s3 then
            match g.head? with
            | some h => do pure !(← concreteS3 h.2.name fuel d)
            | none => pure false
          else pure false
        let missing := byClass || byTrait
        if missing && !atClass then
          ks := ks ++ [.needsAbstract]
          atClass := true
    -- dotc's `checkMemberTypesOK`: a member `d` does not declare is the intersection of what its
    -- direct parents give it, and the member a selection picks must conform to each of them. Only
    -- for a name `d` or an abstract or trait parent declares (through abstract and trait parents:
    -- a concrete parent was checked itself). The pair was checked in a parent and left there by the
    -- cursor (`handledByParent`); this is where dotc finds it again.
    if dl == .s3 then
      for g in sigGroups d.name l do
        let some h := g.head? | continue
        let pub := g.filter (!·.2.priv)
        if pub.any (·.1.1.name == d.name) || !(← declaredUpAbstract h.2.name fuel d) then continue
        let impl? := if ← concreteS3 h.2.name fuel d then pub.find? (!·.2.abs) else pub.head?
        let some impl := impl? | continue
        let mut fromParents : List Hit := []
        for (p, _) in d.parents do
          let lp ← lin fuel (← need p)
          if let some o := pub.find? (isBase lp ·.1.1.name) then fromParents := fromParents ++ [o]
        let bad := fromParents.any fun o => o.1.1.name != impl.1.1.name &&
          !conforms (seenFrom d.name l impl.1.1.name impl.2.res) (seenFrom d.name l o.1.1.name o.2.res)
        if bad && !atClass then
          ks := ks ++ [.resultType]
          atClass := true
  pure (ks.eraseDups.map fun k => { cls := d.name, kind := k })

/-- The errors the compiler reports for a program: those of the earliest phase that has any. -/
def errors (dl : Dialect) (p : Program) : Except String (List Err) := do
  -- the program as the back end sees it: desugared, against the library prelude
  let q := p.desugar dl
  let env := (prelude dl ++ q).env
  let es ← q.flatMap (fun s => s.cls.toList ++ s.obj.toList) |>.mapM fun d =>
    (checkDecl dl d).run.run env
  let es := es.flatten
  match (es.map (·.kind.phase)).min? with
  | some ph => pure (es.filter (·.kind.phase == ph))
  | none => pure []

/-! ## Typer's inheritance checks

Two errors the typer reports for a definition's parents, before refchecks, which then does not run
(scalac 2.12, 2.13 and dotc 3.9, over `FlatRules`' programs): a parent that is a `final` class, and
two instances of one base class with different type arguments. They are not refchecks, so they are
not in `errors` (which `Zinc.Flat.Shared` compares with `Flat`'s refchecks); `reported` puts the two
phases together, as a compiler reports them. -/

/-- The base types `d`'s direct parents give it, each as `d` sees it: (class, type arguments). -/
def parentBases (d : Decl) : M (List (String × List Ty)) := do
  let mut r := []
  for (p, pa) in d.parents do
    let pd ← need p
    let lp ← lin fuel pd
    let w := namedWorld d.name [(pd.name, pa)]
    r := r ++ lp.map fun (a, ts) => (a.name, ts.map (AsSeenFrom.asf w (.this [d.name]) [p]))
  pure r

/-- Do two of `d`'s parents give it different instances of one base class? -/
def baseConflict (d : Decl) : M Bool := do
  let bs ← parentBases d
  pure (bs.any fun (a, ts) => bs.any fun (b, us) => a == b && ts != us)

/-- Does `d` have conflicting base types, through its own parents or inherited from one? -/
def baseConflictDeep : Nat → Decl → M Bool
  | 0, _ => pure false
  | k + 1, d => do
    if ← baseConflict d then return true
    for (p, _) in d.parents do
      if ← baseConflictDeep k (← need p) then return true
    pure false

/-- Typer's errors for `d`. A parent that is a `final` class (scalac: "illegal inheritance from
final class"; dotc: "cannot extend final class"). Different instances of a base class: scalac
reports them where the parents meet ("inherits different type instances"); dotc where a class
or object is instantiable ("cannot be instantiated since it has conflicting base types"), so also
in an object extending such a class, but not in a class that already has a final parent.

Spec: cites SLS §5.1, SLS §5.2
Spec: unspecified SLS §5.1: where a class with two instances of one base class is reported. scalac
reports it where the parents meet; dotc where a class or object is instantiable, so also in an
object extending such a class; calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 on
`Members.membersSpace` and `FlatRules`' 192,000 configurations by
`packages/scala/probes/members.py`. -/
def typerDecl (dl : Dialect) (d : Decl) : M (List Err) := do
  let mut ks : List Kind := []
  let mut finalParent := false
  for (p, _) in d.parents do
    let pd ← need p
    if pd.final && pd.kind != .trt then finalParent := true
  if finalParent then ks := ks ++ [.finalParent]
  let conflict ← if dl == .s3 then
      if d.kind == .trt || d.abs || finalParent then pure false else baseConflictDeep fuel d
    else baseConflict d
  if conflict then ks := ks ++ [.baseTypes]
  pure (ks.map fun k => { cls := d.name, kind := k })

/-- What the compiler reports for a program: typer's errors if there are any, else refchecks'
(`errors`).

Spec: unspecified SLS §5.1.4: that an error in an earlier phase (typer's inheritance checks) hides
refchecks' errors; both compilers stop before refchecks; calibrated against scalac 2.12.21, 2.13.18
and dotc 3.9.0 on `Members.membersSpace` and `FlatRules`' 192,000 configurations by
`packages/scala/probes/members.py`. -/
def reported (dl : Dialect) (p : Program) : Except String (List Err) := do
  let q := p.desugar dl
  let env := (prelude dl ++ q).env
  let ts ← q.flatMap (fun s => s.cls.toList ++ s.obj.toList) |>.mapM fun d =>
    (typerDecl dl d).run.run env
  let ts := ts.flatten
  if ts.isEmpty then errors dl p else pure ts

/-- For each concrete class, the owner of the `m` a selection runs (none if `m` is private).

Spec: cites SLS §5.1.2, SLS §5.1.3 -/
def runs (p : Program) : List (String × String) :=
  p.filterMap fun s => do
    let d ← s.cls
    if d.kind == .trt || d.abs then none
    let r : M (Option Hit) := do
      let l ← lin fuel d
      match (sigGroups d.name l).find? fun g => g.any (·.2.name == "m") with
      | some g => effWinner d.name g
      | none => pure none
    match r.run.run p.env with
    | .ok (some w) => pure (d.name, w.1.1.name)
    | _ => none

/-! ## The calibration space -/

/-- How an owner declares `m: String`. -/
inductive V
  | none | abs | conc | ovr | fin | val | lval | ovrVal | ovrLval | priv | ovrPriv
  deriving DecidableEq, Repr

def V.mem (owner : String) : V → Option Mem
  | V.none => Option.none
  | v =>
    let base : Mem := { name := "m", res := .str, nullary := true, rhs := some s!"\"{owner}\"", ov := some false }
    some <| match v with
      | .abs => { base with abs := true }
      | .ovr => { base with ov := some true }
      | .fin => { base with final := true }
      | .val => { base with isVal := true }
      | .lval => { base with isVal := true, lzy := true }
      | .ovrVal => { base with isVal := true, ov := some true }
      | .ovrLval => { base with isVal := true, lzy := true, ov := some true }
      | .priv => { base with priv := true }
      | .ovrPriv => { base with priv := true, ov := some true }
      | _ => base

/-- `trait T`, `trait U` (extending `T` or not), `abstract class B` (extending `T` or not), and
`class C extends B with T with U`, each declaring `m` one way. -/
def program (t u : V) (uExt : Bool) (b : V) (bExt : Bool) (c : V) : Program :=
  let tD : Decl := { name := "T", kind := .trt, members := (t.mem "T").toList }
  let uD : Decl := { name := "U", kind := .trt, members := (u.mem "U").toList,
                     traits := if uExt then [("T", [])] else [] }
  let bD : Decl := { name := "B", abs := true, members := (b.mem "B").toList,
                     traits := if bExt then [("T", [])] else [] }
  let cD : Decl := { name := "C", abs := c == .abs, members := (c.mem "C").toList,
                     super := some ("B", []),
                     traits := [("T", [])] ++ (if u == .none then [] else [("U", [])]) }
  [{ name := "T", cls := some tD }] ++ (if u == .none then [] else [{ name := "U", cls := some uD }]) ++
    [{ name := "B", cls := some bD }, { name := "C", cls := some cD }]

def V.tag : V → String
  | .none => "-" | .abs => "abs" | .conc => "conc" | .ovr => "ovr" | .fin => "final" | .val => "val"
  | .lval => "lazy" | .ovrVal => "ovrVal" | .ovrLval => "ovrLazy" | .priv => "priv" | .ovrPriv => "ovrPriv"

/-- Each program with a one-line description: how `T`, `U`, `B`, `C` declare `m`. -/
def membersSpace : List (String × Program) :=
  [V.none, .abs, .conc, .fin, .val, .lval].flatMap fun t =>
  ([(V.none, false)] ++ ([V.abs, .conc, .ovr].flatMap fun u => [(u, true), (u, false)])).flatMap fun (u, uExt) =>
  [V.none, .abs, .conc, .ovr, .fin, .val, .priv].flatMap fun b =>
  [true, false].flatMap fun bExt =>
  [V.none, .abs, .conc, .ovr, .ovrVal, .ovrLval, .ovrPriv, .priv].map fun c =>
    (s!"T={t.tag} U={u.tag}{if uExt then "<:T" else ""} B={b.tag}{if bExt then "<:T" else ""} C={c.tag}",
     program t u uExt b bExt c)

/-! ## Witnesses -/

/-- `trait T { def m = "T" }; abstract class B { def m = "B" }; class C extends B with T`. -/
def conflict : Program := program .conc .none false .conc false .none

example : errors .s213 conflict = .ok [{ cls := "C", kind := .conflicting }] := by decide +kernel

/-- With `B extends T` and `B` overriding, the pair is checked in `B`, not again in `C`, and the
selection runs `B`'s `m`. -/
def viaB : Program := program .conc .none false .ovr true .none

example : errors .s213 viaB = .ok [] ∧ runs viaB = [("C", "B")] := by decide +kernel

/-- `override private` is a refchecks error in Scala 2 and an earlier error in Scala 3, which
hides the other programs' refchecks errors. -/
def ovrPriv : Program := program .none .none false .conc false .ovrPriv

example : errors .s213 ovrPriv = .ok [{ cls := "C", kind := .weakerAccess }] := by decide +kernel
example : errors .s3 ovrPriv = .ok [{ cls := "C", kind := .illegalModifiers }] := by decide +kernel

/-- `B extends T` overrides `T`'s concrete `m` without `override`. 2.12 and 3 report it once, in
`B`; 2.13 checks the pair again in `C` and reports conflicting members there too. -/
def recheck : Program := program .conc .none false .conc true .none

example : errors .s212 recheck = .ok [{ cls := "B", kind := .needsOverride }] := by decide +kernel
example : errors .s213 recheck =
    .ok [{ cls := "B", kind := .needsOverride }, { cls := "C", kind := .conflicting }] := by decide +kernel

/-- An abstract `m` in class `B extends T` re-abstracts `T`'s concrete `m`; in trait `U extends T`
it does not, here because `C` also mixes `T` in directly (in Scala 3 a trait's re-abstraction
holds otherwise: `reabsTraitOnly`). -/
def reabsClass : Program := program .conc .none false .abs true .none
def reabsTrait : Program := program .conc .abs true .none false .none

example : errors .s213 reabsClass = .ok [{ cls := "C", kind := .needsAbstract }] := by decide +kernel
example : errors .s213 reabsTrait = .ok [] ∧ runs reabsTrait = [("C", "T")] := by decide +kernel

/-! ## Case classes, through the desugaring

The membership checks run on the desugared program, so a synthesized member is checked like a
written one. `productPrefix` is always synthesized, so a superclass's `final productPrefix` is an
error (scalac 2.13 and 3.9 both report "cannot override final member"); a superclass's `final
toString` is not, because then `toString` is not synthesized. -/

def caseOver (m : Mem) : Program :=
  [{ name := "B", cls := some { name := "B", abs := true, members := [m] } },
   { name := "P", cls := some { name := "P", isCase := true, cparams := [("x", .int)], super := some ("B", []) } }]

example : errors .s213 (caseOver { name := "productPrefix", res := .str, nullary := true, final := true }) =
    .ok [{ cls := "P", kind := .finalOverride }] := by decide +kernel
-- (written without `override`: the model has no `Any`, so `override` would override nothing)
example : errors .s213 (caseOver { name := "toString", res := .str, nullary := true, final := true }) =
    .ok [] := by decide +kernel


/-! ### Re-abstraction and incompatible implementations

Checked against scalac 2.13.18 and dotc 3.9.0 (compiled one by one), each with the verdict both
give; `concreteS3`'s comment has the rule and how it departs from the specification and from Java. -/

/-- A member `m` of type `t`, concrete or abstract. -/
def mem (t : Ty) (abs : Bool) : Mem := { name := "m", res := t, nullary := true, abs := abs }

def decl (n : String) (k : Scala.Kind) (ps : List String) (ms : List Mem) (abs := false) : Src :=
  { name := n, cls := some { name := n, kind := k, abs := abs, members := ms,
                             super := (ps.head?).map (·, []), traits := ps.tail.map (·, []) } }

/-- `class B { def m: String = "" }; trait M { def m: Int }; class C extends B with M`: the
concrete `B.m` implements `M.m` with an incompatible type. Both compilers reject `C`. -/
def implIncompatible : Program :=
  [decl "B" .cls [] [mem .str false], decl "M" .trt [] [mem .int true], decl "C" .cls ["B", "M"] []]

example : errors .s213 implIncompatible = .ok [{ cls := "C", kind := .resultType }] := by decide +kernel
example : errors .s3 implIncompatible = .ok [{ cls := "C", kind := .resultType }] := by decide +kernel

/-- `trait M { def m: String = "" }; trait A extends M { def m: String }; class B extends A`: Scala
2 lets `M.m` implement `m` (as the specification says); Scala 3 rejects `B`. -/
def reabsTraitOnly : Program :=
  [decl "M" .trt [] [mem .str false], decl "A" .trt ["M"] [mem .str true], decl "B" .cls ["A"] []]

example : errors .s213 reabsTraitOnly = .ok [] := by decide +kernel
example : errors .s3 reabsTraitOnly = .ok [{ cls := "B", kind := .needsAbstract }] := by decide +kernel

/-- `class B extends M with A`: with `M` a direct parent, Scala 3 accepts it too. -/
def reabsTraitDirect : Program :=
  [decl "M" .trt [] [mem .str false], decl "A" .trt ["M"] [mem .str true], decl "B" .cls ["M", "A"] []]

example : errors .s213 reabsTraitDirect = .ok [] := by decide +kernel
example : errors .s3 reabsTraitDirect = .ok [] := by decide +kernel

/-- `abstract class A extends M { def m: String }; class B extends A`: a class re-abstracts in both. -/
def reabsAbstractClass : Program :=
  [decl "M" .trt [] [mem .str false], decl "A" .cls ["M"] [mem .str true] (abs := true),
   decl "B" .cls ["A"] []]

example : errors .s213 reabsAbstractClass = .ok [{ cls := "B", kind := .needsAbstract }] := by decide +kernel
example : errors .s3 reabsAbstractClass = .ok [{ cls := "B", kind := .needsAbstract }] := by decide +kernel

/-- `abstract class B extends M { def m: Int }; class C extends B with M`: a class's re-abstraction
holds even with `M` mixed in directly, in both. -/
def reabsClassDirect : Program :=
  [decl "M" .trt [] [mem .int false], decl "B" .cls ["M"] [mem .int true] (abs := true),
   decl "C" .cls ["B", "M"] []]

example : errors .s213 reabsClassDirect = .ok [{ cls := "C", kind := .needsAbstract }] := by decide +kernel
example : errors .s3 reabsClassDirect = .ok [{ cls := "C", kind := .needsAbstract }] := by decide +kernel

/-- `trait A extends M { def m: Int }; abstract class B extends A; class C extends B with M`: a
trait's re-abstraction is undone by a direct parent; both accept `C`. -/
def reabsTraitViaClass : Program :=
  [decl "M" .trt [] [mem .int false], decl "A" .trt ["M"] [mem .int true],
   decl "B" .cls ["A"] [] (abs := true), decl "C" .cls ["B", "M"] []]

example : errors .s213 reabsTraitViaClass = .ok [] := by decide +kernel
example : errors .s3 reabsTraitViaClass = .ok [] := by decide +kernel

/-! ### A pair a parent has, checked again (scala/bug#11136)

`trait IO { def m = "" }; trait SO extends IO { override final def m = "" };
trait SOIO extends IO { override def m = "" }; trait SOSO extends SOIO with SO;
abstract class AS extends SO; class L extends AS with SOSO`. In `SOSO`, `SO.m` overrides `SOIO.m`;
in `L`, whose linearization puts `SOIO` first, `SOIO.m` overrides the final `SO.m`. 2.12 leaves the
pair to the parent `SOSO`, which has both owners, and compiles `L` (its JVM rejects it at run time:
`IncompatibleClassChangeError`); 2.13 checks every pair again (scala/scala#7439); dotc checks it
again because the parent has the owners in the other order (`handledByParent`). -/
def recheck11136 : Program :=
  let conc (ov fin : Bool) : Mem := { mem .str false with ov := some ov, final := fin }
  [decl "IO" .trt [] [conc false false], decl "SO" .trt ["IO"] [conc true true],
   decl "SOIO" .trt ["IO"] [conc true false], decl "SOSO" .trt ["SOIO", "SO"] [],
   decl "AS" .cls ["SO"] [] (abs := true), decl "L" .cls ["AS", "SOSO"] []]

example : errors .s212 recheck11136 = .ok [] := by decide +kernel
example : errors .s213 recheck11136 = .ok [{ cls := "L", kind := .finalOverride }] := by decide +kernel
example : errors .s3 recheck11136 = .ok [{ cls := "L", kind := .finalOverride }] := by decide +kernel

/-- `abstract class B { final def m: String = "" }; abstract class C extends B { def m: String }`:
scalac's cursor pairs them with the concrete `B.m` overriding `C`'s abstract `m`, as SLS §5.1.3 has
it, and nothing fails; dotc's `checkAll` also checks `C.m` as an override of the final `B.m` and
rejects `C`.

Spec: contradicts SLS §5.1.3 / dotc 3.9.0: `abstract class B { final def m: String = "" }; abstract
class C extends B { def m: String }`. By §5.1.3 the concrete `B.m` is the member, and scalac accepts
`C`; dotc's `checkAll` also checks `C.m` as an override of the final `B.m` and rejects `C`
(scala/scala3 neg/i11130; [spec-reabstraction.md](../../../docs/upstream/spec-reabstraction.md)). -/
def abstractOverFinal : Program :=
  [decl "B" .cls [] [{ mem .str false with final := true }] (abs := true),
   decl "C" .cls ["B"] [mem .str true] (abs := true)]

example : errors .s213 abstractOverFinal = .ok [] := by decide +kernel
example : errors .s3 abstractOverFinal = .ok [{ cls := "C", kind := .finalOverride }] := by decide +kernel

end Scala.Members
