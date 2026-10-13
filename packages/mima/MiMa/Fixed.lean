import MiMa.Keys
/-!
# A corrected rule set

MiMa's keys plus five, one per gap in `packages/mima/MiMa/Keys.lean`:

* `resolveMethod c n d`, `resolveField c n d`: for a public class `c` of the old library and every
  name and descriptor, the member a client's reference *through `c`* resolves to (JVMS §5.4.3.2–4,
  private members and superinterfaces included), compared by access, `static`, `abstract` and
  `final`. MiMa compares only the members `c` declares, looked up without private members or
  (for fields) interfaces: gaps MiMa-M1 and MiMa-F1.
* `ifaceField t n d`: an interface that sees a field it did not see before, which a client class
  extending a public class and implementing `t` would resolve before the class's field (MiMa-F2).
* `defaults t n d`: an interface gaining a default method that another public interface, unrelated
  to it, also has (MiMa-D1). In general a client's own interface can have a default of any name, so any
  new default can conflict; in the model's client space, clients implement only library interfaces.
* `subResolves`, `subSelects`, `subOverridesFinal` (MiMa-S1, a method added above a client
  subclass): for a public, non-final class `c`, the declaration of `n d` that a client subclass
  meets first on `c`'s superclass chain is new or changed, and (a) is private or static, so
  resolution of the subclass's `n d` fails where it found an inherited default; (b) is
  package-private or protected, so `invokeinterface` selects it and fails (JVMS §6.5); or (c) is
  public or protected and final, so a subclass that declares `n d` no longer loads. (a) and (b) ask
  that some public interface have a default `n d`: as for D1, the interface is the client's choice,
  and the model's client space is the stand-in. (c) is unconditional.

Soundness on the space: every edit in `BinCompat.edits` that breaks a client of `spaceB` is
reported. Checked by kernel `decide` (enumeration as testing, per `docs/specification.md`; not a proof for
all libraries).
-/

namespace MiMa

open Jvm Jvm.Catalogue Jvm.Clients

inductive Extra
  | resolvedMethodChanged
  | resolvedFieldChanged
  | ifaceFieldShadows
  | defaultConflict
  | subclassResolves
  | subclassSelectsNonPublic
  | subclassOverridesFinal
  deriving DecidableEq, Repr

def Extra.name : Extra → String
  | .resolvedMethodChanged => "ResolvedMethodChanged"
  | .resolvedFieldChanged => "ResolvedFieldChanged"
  | .ifaceFieldShadows => "InterfaceFieldShadows"
  | .defaultConflict => "DefaultConflict"
  | .subclassResolves => "SubclassResolvesNonPublic"
  | .subclassSelectsNonPublic => "SubclassSelectsNonPublic"
  | .subclassOverridesFinal => "SubclassOverridesFinal"

def rank : Access → ℕ | .pub => 3 | .prot => 2 | .pkg => 1 | .priv => 0

/-- Method resolution through `c`, without the access check (§5.4.3.3, §5.4.3.4). -/
def rawResolve (c : C) (n : N) (d : D) : M C N D (C × MethodInfo C N D) := do
  let h ← hdr c
  if h.isInterface then
    match ← askMethod c n d with
    | some i => pure (c, i)
    | none => fromIfaces c n d
  else
    match ← chain false n d depth c with
    | some r => pure r
    | none => fromIfaces c n d

def runIn {α : Type} (l : Lib) (t : M C N D α) : Except LinkError α := t.run.run (answer (world l))

def resolveMethodCheck (o n : Lib) (c : C) (mn : N) (md : D) : Bool :=
  match runIn o (rawResolve c mn md) with
  | .error _ => false
  | .ok (_, i0) =>
    if rank i0.access < 2 then false
    else match runIn n (rawResolve c mn md) with
      | .error _ => true
      | .ok (_, i1) =>
        rank i1.access < rank i0.access || i0.isStatic != i1.isStatic ||
          (!i0.isAbstract && i1.isAbstract) || (!i0.isFinal && i1.isFinal)

def resolveFieldCheck (o n : Lib) (c : C) (fn : N) (fd : D) : Bool :=
  match runIn o (lookupField fn fd depth c) with
  | .error _ | .ok none => false
  | .ok (some (_, f0)) =>
    if rank f0.access < 2 then false
    else match runIn n (lookupField fn fd depth c) with
      | .error _ | .ok none => true
      | .ok (some (_, f1)) =>
        rank f1.access < rank f0.access || f0.isStatic != f1.isStatic || (!f0.isFinal && f1.isFinal)

def declaresField (l : Lib) (t : C) (fn : N) (fd : D) : Bool :=
  (((get l t).map (·.fields)).getD []).any fun f => f.1 = fn ∧ f.2.1 = fd

def isIface (l : Lib) (t : C) : Bool := ((get l t).map (·.header.isInterface)).getD false

/-- `t` is an interface that sees a field `fn` now and saw none before. -/
def ifaceFieldCheck (o n : Lib) (t : C) (fn : N) (fd : D) : Bool :=
  isIface o t && isIface n t && declaresField n t fn fd &&
    (match runIn o (lookupField fn fd depth t) with | .ok (some _) => false | _ => true) &&
    n.any fun (c, cf) =>
      cf.header.isPublic && !cf.header.isInterface && !cf.header.isFinal &&
        !(allIfaces n fuel c).contains t &&
        match runIn n (lookupField fn fd depth c) with
        | .ok (some _) => true
        | _ => false

def isDefault (l : Lib) (t : C) (mn : N) (md : D) : Bool :=
  (meths l t).any fun m => m.1 = mn ∧ m.2.1 = md ∧ !m.2.2.isAbstract ∧ !m.2.2.isStatic

def defaultsCheck (o n : Lib) (t : C) (mn : N) (md : D) : Bool :=
  isIface n t && isDefault n t mn md && !(isIface o t && isDefault o t mn md) &&
    n.any fun (u, cf) =>
      u != t && cf.header.isPublic && cf.header.isInterface && isDefault n u mn md &&
        !(allIfaces n fuel u).contains t && !(allIfaces n fuel t).contains u

/-- A method's flags, without its body. -/
def flags (i : MethodInfo C N D) : Access × Bool × Bool × Bool := (i.access, i.isStatic, i.isAbstract, i.isFinal)

/-- The first declaration of `mn md` on `c`'s superclass chain, of any kind: what resolution
(§5.4.3.3) through a subclass of `c` declaring no `mn md` finds before the superinterfaces. -/
def firstDecl (l : Lib) (c : C) (mn : N) (md : D) : Option (MethodInfo C N D) :=
  ((c :: supers l fuel c).filterMap fun x =>
    ((((get l x).map (·.methods)).getD []).find? fun m => m.1 = mn ∧ m.2.1 = md).map (·.2.2)).head?

/-- The first instance, non-private declaration of `mn md` on `c`'s superclass chain: what
selection (§5.4.6) on a subclass of `c` declaring no `mn md` reaches before the superinterfaces,
and what a subclass's own `mn md` overrides (`overrides` skips static and private methods). -/
def selDecl (l : Lib) (c : C) (mn : N) (md : D) : Option (MethodInfo C N D) :=
  ((c :: supers l fuel c).filterMap fun x =>
    ((meths l x).find? fun m => m.1 = mn ∧ m.2.1 = md ∧ !m.2.2.isStatic).map (·.2.2)).head?

def isPubIface (l : Lib) (u : C) : Bool :=
  ((get l u).map fun cf => cf.header.isPublic && cf.header.isInterface).getD false

/-- Some public interface has a default `mn md`, which a client subclass can inherit. -/
def someDefault (l : Lib) (mn : N) (md : D) : Bool :=
  l.any fun (u, _) => isPubIface l u && isDefault l u mn md

def extendable (l : Lib) (c : C) : Bool :=
  ((get l c).map fun cf => cf.header.isPublic && !cf.header.isInterface && !cf.header.isFinal).getD false

/-- The declaration is new, or its flags changed. -/
def changed (i0 : Option (MethodInfo C N D)) (i1 : MethodInfo C N D) : Bool :=
  (i0.map flags) != some (flags i1)

/-- MiMa-S1 (a), resolution: a subclass of `c` that inherits a default `mn md` resolves
`invokevirtual X.mn` to a new private or static method on `c`'s chain, before the superinterfaces
(`IllegalAccessError`, `IncompatibleClassChangeError`). -/
def subResolvesCheck (o n : Lib) (c : C) (mn : N) (md : D) : Bool :=
  extendable n c && someDefault n mn md &&
    match firstDecl n c mn md with
    | some i1 => (i1.access == .priv || i1.isStatic) && changed (firstDecl o c mn md) i1
    | none => false

/-- MiMa-S1 (b), selection: a subclass of `c` that inherits a default `mn md` selects a new
package-private or protected method on `c`'s chain for `invokeinterface`, which fails
(`IllegalAccessError`, JVMS §6.5). -/
def subSelectsCheck (o n : Lib) (c : C) (mn : N) (md : D) : Bool :=
  extendable n c && someDefault n mn md &&
    match selDecl n c mn md with
    | some i1 => (i1.access == .pkg || i1.access == .prot) && changed (selDecl o c mn md) i1
    | none => false

/-- MiMa-S1 (c), loading: `c`'s chain newly has a public or protected final `mn md`, which a client
subclass declaring `mn md` now overrides (§5.3.5). Unconditional: any client subclass may declare it. -/
def subOverridesFinalCheck (o n : Lib) (c : C) (mn : N) (md : D) : Bool :=
  extendable n c &&
    match selDecl n c mn md with
    | some i1 =>
      i1.isFinal && (i1.access == .pub || i1.access == .prot) &&
        !((selDecl o c mn md).map (·.isFinal)).getD false
    | none => false

def allN : List N := [.m]
def allMD : List D := [.v, .i]
def allFD : List D := [.s]

/-- The extra problems, per class public in the old library. -/
def extra (o n : Lib) : List Extra :=
  o.flatMap fun (c, cf) =>
    if !cf.header.isPublic then []
    else
      (allN.flatMap fun mn => allMD.filterMap fun md =>
        if resolveMethodCheck o n c mn md then some .resolvedMethodChanged else none) ++
      (allN.flatMap fun fn => allFD.filterMap fun fd =>
        if resolveFieldCheck o n c fn fd then some .resolvedFieldChanged else none) ++
      (allN.flatMap fun fn => allFD.filterMap fun fd =>
        if ifaceFieldCheck o n c fn fd then some .ifaceFieldShadows else none) ++
      (allN.flatMap fun mn => allMD.filterMap fun md =>
        if defaultsCheck o n c mn md then some .defaultConflict else none) ++
      (allN.flatMap fun mn => allMD.flatMap fun md =>
        (if subResolvesCheck o n c mn md then [.subclassResolves] else []) ++
        (if subSelectsCheck o n c mn md then [.subclassSelectsNonPublic] else []) ++
        (if subOverridesFinalCheck o n c mn md then [.subclassOverridesFinal] else []))

/-- The corrected rule set reports something. -/
def fixedReports (o n : Lib) : Bool := mima o n != [] || extra o n != []

/-- Each witness of a MiMa gap is reported by the corrected rules. -/
example : [finalField, shadowStatic, shadowField, overridePrivate, ifaceField, defaultConflict,
    protectedRemoved, privateAboveDefault, pkgAboveDefault, finalAboveOverride].all
    (fun x => fixedReports x.o x.n) = true := by decide +kernel

/-- Track J7's `pkgMethodAboveDefault` (MiMa-S1), which MiMa misses. -/
example : fixedReports pkgMethodAboveDefault.v0 pkgMethodAboveDefault.v1 = true := by decide +kernel

/-! ## Package-private members: `methodBecomesFinalBehind`

Track J6's `methodBecomesFinalBehind` makes a package-private `A.m` final behind a public `B.m` in
another package; the client's `X`, in `A`'s package, overrides both and no longer loads. The corrected
rules are silent, as MiMa is: through `A` the method is package-private, so neither MiMa nor
`resolveMethod` keys it, and through `B` it resolves to `B.m`, which is unchanged. A package-private
member is visible only in its run-time package, so the only clients it can break are classes another
JAR adds to the library's package (a split package). That is a scope line, not a gap. -/

example : fixedReports methodBecomesFinalBehind.v0 methodBecomesFinalBehind.v1 = false ∧
    methodBecomesFinalBehind.after = .error .finalOverride := by decide +kernel

/-- `A.m` made final in a library of `Jvm.Clients.chainSpace`. -/
def finalA (l : Lib) : Lib :=
  l.map fun (c, cf) => if c = .A then (c, { cf with methods := cf.methods.map fun (n, d, i) => (n, d, { i with isFinal := true }) }) else (c, cf)

/-- The edit space of `methodBecomesFinalBehind`'s shape over the chain space, whose clients are
outside the library's packages (`X` in the unnamed package): each program whose `A.m` is not final,
with `A.m` made final in `v1`. -/
def finalBehindEdits : List Case :=
  (chainSpace.filter fun k => !(k.v0.any fun (c, cf) => c = .A && cf.methods.any (·.2.2.isFinal))).map
    fun k => { k with name := k.name ++ "/final", v1 := finalA k.v0 }

/-- The library's own classes load on `l`. -/
def libLoads (l : Lib) : Bool := links (world l) { loads := l.map (·.1) }

/-- An edit of `finalBehindEdits` that breaks its client, that the corrected rules miss, and whose
library still loads by itself. `lake exe bincompat finalBehind` finds none (too large a space for
kernel `decide` in the build). -/
def finalBehindMissed (k : Case) : Bool :=
  links k.w0 k.prog && !links k.w1 k.prog && !fixedReports k.v0 k.v1 && libLoads k.v1

/-! ## The edit space, indexed for `packages/mima/MiMa/Sound.lean` -/


def baseOf : ℕ → Lib | 1 => base1 | 3 => base3 | _ => base2

/-- The `i`-th variant of class `c` in base `b`. -/
def variant (b : ℕ) (c : C) (i : ℕ) : Lib :=
  let l := baseOf b
  match get l c with
  | some cf => match (variants c cf)[i]? with
    | some cf' => replace l c cf'
    | none => l
  | none => l

/-- The same library: not an edit. -/
def same (o n : Lib) : Bool :=
  o.map (·.2.header) == n.map (·.2.header) && o.map (·.2.methods) == n.map (·.2.methods) &&
    o.map (·.2.fields) == n.map (·.2.fields)

/-- The variant is not a well-formed edit, or the corrected rules report it, or no client breaks. -/
def sound (b : ℕ) (c : C) (i : ℕ) : Bool :=
  let o := baseOf b
  let n := variant b c i
  !wf n || same o n || fixedReports o n ||
    !breaksSomeClient { name := "", mima := none, v0 := o, v1 := n, prog := {} } spaceB

/-- How many variants a class has. -/
def nVariants (b : ℕ) (c : C) : ℕ := ((get (baseOf b) c).map (variants c ·)).getD [] |>.length

/-- The variants that are well-formed edits the corrected rules do not report: these are run
against every client, one `example` each; the rest are sound without running a client. -/
def unreported (b : ℕ) (c : C) : List ℕ :=
  (List.range (nVariants b c)).filter fun i =>
    let n := variant b c i
    wf n && !same (baseOf b) n && !fixedReports (baseOf b) n

end MiMa
