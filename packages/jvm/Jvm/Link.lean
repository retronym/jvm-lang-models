import Query.Basic
import Query.Task
/-!
# JVM linkage as a query tree

A client links against a class table: loading checks a class's supertypes, and each call site
resolves a symbolic reference (JVMS §5.4.3.3 for a class, §5.4.3.4 for an interface) and then
selects a method on the receiver's class (§5.4.6); fields resolve by §5.4.3.2, and access is
checked by §5.4.4 and the verifier's rules for receivers, `invokespecial` and protected members. The
model writes linking as a `Task` whose queries are the class table's entries: a class's header,
and whether it declares a method or field of a name and descriptor. So linking has a trace, the *linkage footprint*, and T1 applies to it
unchanged: a library edit that agrees with the old library on a client's footprint links that
client the same way (`link_congr`).

That is the bridge to Zinc. Zinc asks whether a source must be *recompiled*; binary
compatibility asks whether its old classfile still *links* (and selects the same methods) against
the new library. Both are questions about a task's trace against an edited environment.

The model is generic in class, method-name and descriptor types. Calibrated against HotSpot 21, 25
and 27 by `packages/jvm/probes`. A method's body is its linkage behaviour (Track J4): the sites it runs, in
order, with `this` as a receiver; a program's outcome is the sequence of methods it enters. Private access
extends to nestmates (§5.4.4). Not modelled: data and control flow in bodies, constructor chaining
(a constructor's implicit `super(…)` call), signature-polymorphic methods, `Object`'s methods in interface
resolution, loader constraints, class initialisation, protected constructors and modules (all classes are in one). Linking is lazy, as on the JVM: an error is raised by
the first site that hits it; a class is loaded, with its loading checks, when it is first referred
to, and each site is verified just before it runs (as if each site were its own method).
-/

open Query

namespace Jvm

variable {C N D : Type} [DecidableEq C] [DecidableEq N] [DecidableEq D]

/-- A member's access (JVMS §4.6, §5.4.4). -/
inductive Access | pub | prot | pkg | priv
  deriving DecidableEq, Repr

/-- `pkg` is the class's runtime package (0 is the unnamed one). A class's package is part of its
name, so it must not differ between the class tables a model compares. -/
structure Header (C : Type) where
  isInterface : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  super : Option C := none
  ifaces : List C := []
  isPublic : Bool := true
  pkg : Nat := 0
  /-- The `PermittedSubclasses` attribute: `some ps` for a sealed class or interface. -/
  permitted : Option (List C) := none
  /-- The `NestHost` attribute: the class that claims to be this class's nest host. -/
  nestHost : Option C := none
  /-- The `NestMembers` attribute of a nest host. -/
  nestMembers : List C := []
  deriving DecidableEq, Repr

/-- A call site, as javac emits it for `new R().m()` with the static receiver type `C` (an upcast
`C c = new R(); c.m()` when `R ≠ C`), or a `new C()` whose constructor is not modelled (`construct`
models one); field accesses likewise.
`invokespecial` is a `super` call (`iface` for `I.super.m()`) from the site's class, so it is wrapped in a
`within`. `within x s` runs `s` from a static method of the client's class `x`. -/
inductive Site (C N D : Type)
  | invokestatic (c : C) (n : N) (d : D)
  | invokevirtual (c : C) (n : N) (d : D) (recv : C)
  | invokeinterface (c : C) (n : N) (d : D) (recv : C)
  | new (c : C)
  /-- `invokestatic` of an interface method (an `InterfaceMethodref`). -/
  | invokestaticIface (c : C) (n : N) (d : D)
  | invokespecial (c : C) (n : N) (d : D) (iface : Bool)
  | getfield (c : C) (n : N) (d : D) (recv : C)
  | putfield (c : C) (n : N) (d : D) (recv : C)
  | getstatic (c : C) (n : N) (d : D)
  | putstatic (c : C) (n : N) (d : D)
  | within (x : C) (s : Site C N D)
  /-- `new c(…)`: `new c; dup; invokespecial c.n d`, where `n` is the constructor's name (`<init>`)
  in the caller's name type. -/
  | construct (c : C) (n : N) (d : D)
  /-- `this.m()` in a method body: `aload_0; invokevirtual c.n d`. The receiver is the run's `this`
  (Track J4); outside an instance method's body there is none, and the verifier rejects the site. -/
  | invokevirtualThis (c : C) (n : N) (d : D)
  /-- `aload_0; invokeinterface c.n d`, on the run's `this`. -/
  | invokeinterfaceThis (c : C) (n : N) (d : D)
  /-- `aload_0; getfield c.n d`, on the run's `this`. -/
  | getfieldThis (c : C) (n : N) (d : D)
  /-- `aload_0; …; putfield c.n d`, on the run's `this`. -/
  | putfieldThis (c : C) (n : N) (d : D)
  deriving DecidableEq, Repr

/-- A method's flags and its body. The body is the method's linkage behaviour (Track J4): the sites it
runs, in order, when it runs straight through once; no data, no control flow. Empty by default. -/
structure MethodInfo (C N D : Type) where
  isStatic : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  access : Access := .pub
  body : List (Site C N D) := []
  deriving DecidableEq, Repr

structure FieldInfo where
  isStatic : Bool := false
  isFinal : Bool := false
  access : Access := .pub
  deriving DecidableEq, Repr

structure Classfile (C N D : Type) where
  header : Header C := {}
  methods : List (N × D × MethodInfo C N D) := []
  fields : List (N × D × FieldInfo) := []
  deriving Repr

/-- A class table: the library's classfiles and the client's. -/
abbrev World (C N D : Type) := C → Option (Classfile C N D)

inductive Q (C N D : Type)
  | header (c : C)
  | method (c : C) (n : N) (d : D)
  | declared (c : C)
  | field (c : C) (n : N) (d : D)
  deriving DecidableEq, Repr

def Ans {C N D : Type} : Q C N D → Type
  | .header _ => Option (Header C)
  | .method .. => Option (MethodInfo C N D)
  | .declared _ => List (N × D × MethodInfo C N D)
  | .field .. => Option FieldInfo

def answer (w : World C N D) : (q : Q C N D) → Ans q
  | .header c => (w c).map (·.header)
  | .method c n d => (w c).bind fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
  | .declared c => ((w c).map (·.methods)).getD []
  | .field c n d => (w c).bind fun cf => (cf.fields.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)

/-- Do two class tables give the same answer to `q`? -/
def agrees (w w' : World C N D) : Q C N D → Bool
  | .header c => decide ((w c).map (·.header) = (w' c).map (·.header))
  | .method c n d =>
    let f : Classfile C N D → Option (MethodInfo C N D) :=
      fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
    decide ((w c).bind f = (w' c).bind f)
  | .declared c => decide (((w c).map (·.methods)).getD [] = ((w' c).map (·.methods)).getD [])
  | .field c n d =>
    let f : Classfile C N D → Option FieldInfo :=
      fun cf => (cf.fields.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
    decide ((w c).bind f = (w' c).bind f)

theorem agrees_iff (w w' : World C N D) (q : Q C N D) :
    agrees w w' q = true ↔ answer w q = answer w' q := by
  cases q <;> simp only [agrees, answer, decide_eq_true_eq] <;> exact Iff.rfl

/-- The `LinkageError`s the model raises. `packages/jvm/probes/Run.java` maps each to the JVM's class, calibrated on
HotSpot 21, 25 and 27: `finalSuper` and `finalOverride` are `IncompatibleClassChangeError`s. -/
inductive LinkError
  | noClassDef
  | incompatibleClassChange
  | noSuchMethod
  | abstractMethod
  | instantiation
  | finalSuper
  | finalOverride
  /-- A receiver not assignable to the site's owner, or a bad `invokespecial`: the verifier rejects
  the client. -/
  | verify
  /-- A class or member the site's class may not access (§5.4.4), or a write to a final field. -/
  | illegalAccess
  | noSuchField
  /-- The run entered methods more than `fuel` deep: not an error the JVM throws, but the model's
  bound on a body that calls itself back. -/
  | outOfFuel
  deriving DecidableEq, Repr

abbrev L (C N D : Type) := Query.Task (Q C N D) Ans

abbrev M (C N D : Type) := ExceptT LinkError (L C N D)

def askHeader (c : C) : M C N D (Option (Header C)) :=
  ExceptT.lift (Query.Task.ask (.header c) Query.Task.pure : L C N D (Option (Header C)))

def askMethod (c : C) (n : N) (d : D) : M C N D (Option (MethodInfo C N D)) :=
  ExceptT.lift (Query.Task.ask (.method c n d) Query.Task.pure : L C N D (Option (MethodInfo C N D)))

def askDeclared (c : C) : M C N D (List (N × D × MethodInfo C N D)) :=
  ExceptT.lift (Query.Task.ask (.declared c) Query.Task.pure : L C N D (List (N × D × MethodInfo C N D)))

def askField (c : C) (n : N) (d : D) : M C N D (Option FieldInfo) :=
  ExceptT.lift (Query.Task.ask (.field c n d) Query.Task.pure : L C N D (Option FieldInfo))

def hdr (c : C) : M C N D (Header C) := do
  match ← askHeader c with
  | some h => pure h
  | none => throw .noClassDef

/-- Bound on the depth of a hierarchy walk. -/
def depth : Nat := 6

/-- The superinterfaces of `c`, through its superclasses and transitively; with repeats. -/
def ifacesOf : Nat → C → M C N D (List C)
  | 0, _ => pure []
  | k + 1, c => do
    let h ← hdr c
    let up ← match h.super with
      | none => pure []
      | some s => ifacesOf k s
    let ii ← h.ifaces.mapM fun i => do
      let r ← ifacesOf k i
      pure (i :: r)
    pure (ii.flatten ++ up)

/-- `x` is `c` or a subclass of `c`, by superclasses. -/
def subclassOf (c : C) : Nat → C → M C N D Bool
  | 0, _ => pure false
  | k + 1, x => do
    if x = c then return true
    match (← hdr x).super with
    | none => pure false
    | some s => subclassOf c k s

/-- Look a method up in `c` and its superclasses (resolution, §5.4.3.3 step 2, which finds static
and private methods too). -/
def chain (inst : Bool) (n : N) (d : D) : Nat → C → M C N D (Option (C × MethodInfo C N D))
  | 0, _ => pure none
  | k + 1, c => do
    let h ← hdr c
    match ← askMethod c n d with
    | some i =>
      if inst && i.isStatic then
        match h.super with
        | none => pure none
        | some s => chain inst n d k s
      else pure (some (c, i))
    | none =>
      match h.super with
      | none => pure none
      | some s => chain inst n d k s

/-- The superclasses of `c` (from `c` itself) before `a`, if `a` is one of them. -/
def below (a : C) : Nat → C → M C N D (Option (List C))
  | 0, _ => pure none
  | k + 1, c => do
    if c = a then return some []
    match (← hdr c).super with
    | none => pure none
    | some s => pure ((← below a k s).map (c :: ·))

/-- Can `(x, mi)` override `(a, ma)`, both named `n` with descriptor `d` (§5.4.5)? Private and
static methods neither override nor are overridden. A package-private `ma` is overridden from its
own run-time package, or (case (b)) through a method `mb` of a class between them that `mi` can
override and that can override `ma`. -/
def overridesK (n : N) (d : D) : Nat → C → MethodInfo C N D → C → MethodInfo C N D → M C N D Bool
  | 0, _, _, _, _ => pure false
  | k + 1, x, mi, a, ma => do
    if mi.isStatic || mi.access = .priv || ma.isStatic || ma.access = .priv then return false
    if ma.access != .pkg then return true
    if (← hdr x).pkg = (← hdr a).pkg then return true
    let some s := (← hdr x).super | return false
    let some bs ← below a depth s | return false
    for b in bs do
      if let some mb ← askMethod b n d then
        if (← overridesK n d k x mi b mb) && (← overridesK n d k b mb a ma) then return true
    return false

/-- `overridesK` with the hierarchy's depth bound. -/
def overrides (n : N) (d : D) (x : C) (mi : MethodInfo C N D) (a : C) (ma : MethodInfo C N D) :
    M C N D Bool :=
  overridesK n d depth x mi a ma

/-- Selection's walk (§5.4.6 step 2): the first declaration in `c` or a superclass that overrides
the resolved method `(a, ma)`. -/
def chainOver (n : N) (d : D) (a : C) (ma : MethodInfo C N D) :
    Nat → C → M C N D (Option (C × MethodInfo C N D))
  | 0, _ => pure none
  | k + 1, c => do
    let h ← hdr c
    let here ← match ← askMethod c n d with
      | some i => if c = a then pure (some (c, i))
                  else if ← overrides n d c i a ma then pure (some (c, i)) else pure none
      | none => pure none
    match here with
    | some r => pure (some r)
    | none =>
      match h.super with
      | none => pure none
      | some s => chainOver n d a ma k s

/-- May `x` (with header `h`) extend or implement `s` (with header `hs`)? JVMS §5.3.5: if `s` is
sealed, `x` must be listed in its `PermittedSubclasses` and, unless `x` is public, be in the same
run-time package (all classes here are in one module). -/
def permits (x : C) (h hs : Header C) : Bool :=
  match hs.permitted with
  | none => true
  | some ps => (h.isPublic || h.pkg == hs.pkg) && ps.contains x

/-- The final instance methods named `n` with descriptor `d` declared in `c` or a superclass. -/
def finalsAbove (n : N) (d : D) : Nat → C → M C N D (List (C × MethodInfo C N D))
  | 0, _ => pure []
  | k + 1, c => do
    let here := match ← askMethod c n d with
      | some i => if i.isFinal && !i.isStatic then [(c, i)] else []
      | none => []
    match (← hdr c).super with
    | none => pure here
    | some s => pure (here ++ (← finalsAbove n d k s))

/-- Load a class, and first its superinterfaces and superclass (HotSpot's class file parser resolves
them in that order): each superinterface must be an interface, the superclass a non-final class,
both accessible from the class and, if sealed, permitting it (§5.3.5), and none of the class's instance methods may override a final one. The JVM loads a class when a
site, the verifier or a subclass first refers to it; the model loads it at each such reference,
which repeats queries but not answers. -/
def loadK : Nat → C → M C N D Unit
  | 0, _ => pure ()
  | k + 1, x => do
    let h ← hdr x
    for i in h.ifaces do
      loadK k i
      if !(← hdr i).isInterface then throw .incompatibleClassChange
    match h.super with
    | none =>
      for i in h.ifaces do
        if !permits x h (← hdr i) then throw .incompatibleClassChange
    | some s =>
      loadK k s
      let hs ← hdr s
      if hs.isInterface then throw .incompatibleClassChange
      if hs.isFinal then throw .finalSuper
      if !permits x h hs then throw .incompatibleClassChange
      if !hs.isPublic && hs.pkg != h.pkg then throw .illegalAccess
      for i in h.ifaces do
        let hi ← hdr i
        if !permits x h hi then throw .incompatibleClassChange
        if !hi.isPublic && hi.pkg != h.pkg then throw .illegalAccess
      for (n, d, mi) in ← askDeclared x do
        -- §5.3.5: any final method of a superclass, not only the nearest declaration
        for (a, si) in ← finalsAbove n d depth s do
          if ← overrides n d x mi a si then throw .finalOverride

def load (x : C) : M C N D Unit := loadK depth x

/-- A class's header, after loading it. -/
def cls (c : C) : M C N D (Header C) := do
  load c
  hdr c

/-- The class whose code executes a site: `none` is a class of its own in the unnamed package. -/
abbrev Cur (C : Type) := Option C

def curPkg : Cur C → M C N D Nat
  | none => pure 0
  | some x => do pure (← hdr x).pkg

/-- Resolve a class reference from `cur` (§5.4.3.1): load it, and check it is accessible. -/
def resolveCls (cur : Cur C) (c : C) : M C N D (Header C) := do
  let h ← cls c
  if !h.isPublic && h.pkg != (← curPkg cur) then throw .illegalAccess
  pure h

/-- The nest host of `c` (JVMS §5.4.4): the class its `NestHost` attribute names, if that class is
present, in `c`'s run-time package and lists `c` in its `NestMembers`; otherwise `c` itself (since
JDK 15 a failed nest-host check is not an error, `c` is just alone in its nest). -/
def nestHostOf (c : C) : M C N D C := do
  let h ← hdr c
  let some n := h.nestHost | return c
  match ← askHeader n with
  | some hn => pure (if hn.pkg = h.pkg && hn.nestMembers.contains c then n else c)
  | none => pure c

/-- Member access from `cur` to a member of `decl` (§5.4.4). A private member is accessible from its
own class and from the classes of its nest: `cur` and `decl` have the same nest host. -/
def accessible (cur : Cur C) (decl : C) (acc : Access) : M C N D Bool := do
  match acc with
  | .pub => pure true
  | .priv =>
    match cur with
    | none => pure false
    | some x => if x = decl then pure true else pure ((← nestHostOf x) = (← nestHostOf decl))
  | .pkg => pure ((← hdr decl).pkg = (← curPkg cur))
  | .prot =>
    if (← hdr decl).pkg = (← curPkg cur) then return true
    match cur with
    | none => pure false
    | some x => subclassOf decl depth x

/-- The maximally-specific superinterface methods of `c` for `n` and `d` (§5.4.3.3): instance
methods, not private, declared in a superinterface of `c` that no other such method's interface
extends. -/
def maxSpecific (c : C) (n : N) (d : D) : M C N D (List (C × MethodInfo C N D)) := do
  let is ← ifacesOf depth c
  -- Mathlib's `dedup` keeps the last occurrence of each interface; so does this.
  let cands ← (Query.dedupLast is).filterMapM fun i => do
    let m ← askMethod i n d
    pure ((m.filter fun mi => !mi.isStatic && mi.access != .priv).map fun mi => (i, mi))
  cands.filterM fun p => do
    let below ← cands.anyM fun q => do
      if q.1 = p.1 then pure false
      else pure ((← ifacesOf depth q.1).contains p.1)
    pure !below

/-- Step 3 of §5.4.3.3 and §5.4.3.4: a unique non-abstract maximally-specific method, else any
superinterface method. -/
def fromIfaces (c : C) (n : N) (d : D) : M C N D (C × MethodInfo C N D) := do
  let ms ← maxSpecific c n d
  match ms.filter fun p => !p.2.isAbstract with
  | [r] => pure r
  | _ =>
    match ms with
    | r :: _ => pure r
    | [] => throw .noSuchMethod

def checkAccess (cur : Cur C) (r : C × MethodInfo C N D) : M C N D (C × MethodInfo C N D) := do
  if !(← accessible cur r.1 r.2.access) then throw .illegalAccess
  pure r

/-- Method resolution against a class, §5.4.3.3. -/
def resolveClass (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × MethodInfo C N D) := do
  let h ← resolveCls cur c
  if h.isInterface then throw .incompatibleClassChange
  match ← chain false n d depth c with
  | some r => checkAccess cur r
  | none => checkAccess cur (← fromIfaces c n d)

/-- Interface method resolution, §5.4.3.4. -/
def resolveIface (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × MethodInfo C N D) := do
  let h ← resolveCls cur c
  if !h.isInterface then throw .incompatibleClassChange
  match ← askMethod c n d with
  | some i => checkAccess cur (c, i)
  | none => checkAccess cur (← fromIfaces c n d)

/-- Method selection on the receiver's class `r` for the resolved method `(a, ma)`, §5.4.6, with
`invokevirtual`'s and (`iface`) `invokeinterface`'s errors. A private resolved method is selected
itself. `invokeinterface` also fails if it selects a method that is neither public nor private (JVMS
§6.5), before the check for an abstract one: a package-private class method can override a public
interface method (§5.4.5) but not run for it. -/
def select (iface : Bool) (r : C) (n : N) (d : D) (a : C) (ma : MethodInfo C N D) : M C N D C := do
  if ma.access = .priv then return a
  match ← chainOver n d a ma depth r with
  | some (o, i) =>
    if iface && (i.access = .pkg || i.access = .prot) then throw .illegalAccess
    if i.isAbstract then throw .abstractMethod else pure o
  | none =>
    let ms ← maxSpecific r n d
    match ms.filter fun p => !p.2.isAbstract with
    | [p] => pure p.1
    | [] => throw .abstractMethod
    | _ => throw .incompatibleClassChange

/-- Field resolution, §5.4.3.2: `c`, then its superinterfaces, then its superclass. -/
def lookupField (n : N) (d : D) : Nat → C → M C N D (Option (C × FieldInfo))
  | 0, _ => pure none
  | k + 1, c => do
    if let some f ← askField c n d then return some (c, f)
    let h ← hdr c
    for i in h.ifaces do
      if let some r ← lookupField n d k i then return some r
    match h.super with
    | none => pure none
    | some s => lookupField n d k s

def resolveField (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × FieldInfo) := do
  discard <| resolveCls cur c
  match ← lookupField n d depth c with
  | none => throw .noSuchField
  | some (a, f) =>
    if !(← accessible cur a f.access) then throw .illegalAccess
    pure (a, f)

/-- The verifier's assignability of class type `r` to `c` (JVMS §4.10.1.2, as HotSpot checks it):
equal names pass without loading; otherwise `c` is loaded, an interface passes, and a class must be
a superclass of `r`. -/
def assignable (r c : C) : M C N D Unit := do
  if r = c then return
  if (← cls c).isInterface then return
  discard <| cls r
  if !(← subclassOf c depth r) then throw .verify

/-- `new c`: resolve it; it must be a concrete class. -/
def instantiate (cur : Cur C) (c : C) : M C N D Unit := do
  let h ← resolveCls cur c
  if h.isInterface || h.isAbstract then throw .instantiation

/-- The verifier's rule for `invokespecial` from `x` to `c` (HotSpot's `verify_invoke_instructions`):
`x` itself, its direct superclass or a direct superinterface pass by name; otherwise `x` must be
assignable to `c`, and `c` must not be an interface (an indirect superinterface). Calibrated on
HotSpot 25+: what matters is whether `c` is an interface, not the constant's tag; an
`InterfaceMethodref` to a class passes here and fails in resolution. HotSpot 21 checked the tag
instead (JDK-8350029, fixed in 25). -/
def verifySpecial (x c : C) : M C N D Unit := do
  let h ← hdr x
  if c = x || h.super = some c || h.ifaces.contains c then return
  assignable x c
  if (← hdr c).isInterface then throw .verify

/-- The verifier's protected check (§4.10.1.8, HotSpot's `verify_protected_access`): from `x`, a
reference through a proper superclass `c` of `x` to a protected member declared in another package
needs a receiver `r` that is an `x`. `acc` looks the member up from `c`. -/
def verifyProtected (cur : Cur C) (c r : C) (acc : M C N D (Option (C × Access))) :
    M C N D Unit := do
  let some x := cur | return
  if c = x then return
  let some s := (← hdr x).super | return
  if !(← subclassOf c depth s) then return
  let some (a, .prot) ← acc | return
  if (← hdr a).pkg = (← hdr x).pkg then return
  if !(← subclassOf x depth r) then throw .verify

/-- The class whose code runs a `this` site and the class of `this`: the verifier rejects `aload_0`
outside an instance method's body. -/
def thisOf (cur : Cur C) (self : Option C) : M C N D (C × C) :=
  match cur, self with
  | some x, some t => pure (x, t)
  | _, _ => throw .verify

/-- Enter the method `n d` of `o`, the class resolution or selection chose, on the receiver `self`
(`none` for a static method): the entry itself, then the method's body, each site run from `o` by
`run` (Track J4). -/
def enter (run : Cur C → Option C → Site C N D → M C N D (List C)) (o : C) (n : N) (d : D)
    (self : Option C) : M C N D (List C) := do
  let body := ((← askMethod o n d).map (·.body)).getD []
  let l ← body.mapM (run (some o) self)
  pure (o :: l.flatten)

/-- Execute a site from `cur`, with `self` the class of `this` (`none` outside an instance method's
body); a method the site selects is entered with `enter'`, and a new instance's constructor run with
`init'`. A static method entered from a body keeps the caller's `this`: the static helpers that take
the receiver as their first argument (Scala's `$init$` and `m$`) see it as `aload_0`. The result is the sequence of methods
entered, or for a site that enters none, the class whose field is accessed or that is instantiated.
The verifier checks the receiver's upcast before the site runs; then the receiver is instantiated,
the member resolved and selected. -/
def runSiteWith (enter' : C → N → D → Option C → M C N D (List C)) (init' : C → M C N D Unit)
    (cur : Cur C) (self : Option C) : Site C N D → M C N D (List C)
  | .invokestatic c n d => do
    let (o, i) ← resolveClass cur c n d
    if !i.isStatic then throw .incompatibleClassChange
    enter' o n d self
  | .invokestaticIface c n d => do
    let (o, i) ← resolveIface cur c n d
    if !i.isStatic then throw .incompatibleClassChange
    enter' o n d self
  | .invokevirtual c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← chain false n d depth c).map fun (a, i) => (a, i.access))
    instantiate cur r
    init' r
    let (a, i) ← resolveClass cur c n d
    if i.isStatic then throw .incompatibleClassChange
    enter' (← select false r n d a i) n d (some r)
  | .invokeinterface c n d r => do
    assignable r c
    instantiate cur r
    init' r
    let (a, i) ← resolveIface cur c n d
    if i.isStatic then throw .incompatibleClassChange
    if !(← ifacesOf depth r).contains c then throw .incompatibleClassChange
    enter' (← select true r n d a i) n d (some r)
  | .new c => do
    instantiate cur c
    init' c
    pure [c]
  | .invokespecial c n d iface => do
    -- `this` is an instance of the site's class.
    let x ← match cur with
      | some x => pure x
      | none => throw .verify
    verifySpecial x c
    -- In an instance method's body the receiver is `this`; otherwise a new `x`.
    let t ← match self with
      | some t => pure t
      | none => do instantiate cur x; init' x; pure x
    let (a, i) ← if iface then resolveIface cur c n d else resolveClass cur c n d
    if i.isStatic then throw .incompatibleClassChange
    let hc ← hdr c
    let start ← if !hc.isInterface && c != x && (← subclassOf c depth x) then
        match (← hdr x).super with
        | some s => pure s
        | none => pure c
      else pure c
    let o ← match ← chain true n d depth start with
      | some (o, i) => if i.isAbstract then throw .abstractMethod else pure o
      | none =>
        let ms ← maxSpecific start n d
        match ms.filter fun p => !p.2.isAbstract with
        | [p] => pure p.1
        | [] => if i.isAbstract then throw .abstractMethod else pure a
        | _ => throw .incompatibleClassChange
    enter' o n d (some t)
  | .getfield c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    instantiate cur r
    init' r
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    pure [a]
  | .putfield c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    instantiate cur r
    init' r
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    if f.isFinal then throw .illegalAccess
    pure [a]
  | .getstatic c n d => do
    let (a, f) ← resolveField cur c n d
    if !f.isStatic then throw .incompatibleClassChange
    pure [a]
  | .putstatic c n d => do
    let (a, f) ← resolveField cur c n d
    if !f.isStatic then throw .incompatibleClassChange
    if f.isFinal then throw .illegalAccess
    pure [a]
  | .within x s => do
    discard <| resolveCls cur x
    runSiteWith enter' init' (some x) none s
  | .construct c n d => do
    instantiate cur c
    -- Resolution walks the superclasses as for any method, with its access check; then the
    -- constructor must be declared by `c` itself (JVMS §6.5 `invokespecial`, linking exceptions;
    -- HotSpot's `linktime_resolve_special_method`).
    let (a, _) ← resolveClass cur c n d
    if a != c then throw .noSuchMethod
    enter' c n d (some c)
  | .invokevirtualThis c n d => do
    let (x, t) ← thisOf cur self
    assignable x c
    verifyProtected cur c x do
      pure ((← chain false n d depth c).map fun (a, i) => (a, i.access))
    let (a, i) ← resolveClass cur c n d
    if i.isStatic then throw .incompatibleClassChange
    enter' (← select false t n d a i) n d (some t)
  | .invokeinterfaceThis c n d => do
    let (x, t) ← thisOf cur self
    assignable x c
    let (a, i) ← resolveIface cur c n d
    if i.isStatic then throw .incompatibleClassChange
    if !(← ifacesOf depth t).contains c then throw .incompatibleClassChange
    enter' (← select true t n d a i) n d (some t)
  | .getfieldThis c n d => do
    let (x, _) ← thisOf cur self
    assignable x c
    verifyProtected cur c x do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    pure [a]
  | .putfieldThis c n d => do
    let (x, _) ← thisOf cur self
    assignable x c
    verifyProtected cur c x do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    if f.isFinal then throw .illegalAccess
    pure [a]

/-- Bound on the depth of nested method entries: a body may call a method whose body calls it back.
The spaces' bodies are a site or two deep, so the bound only keeps the run total. -/
def fuel : Nat := 8

/-- Run the constructor `init` (a name and descriptor) of a new instance of `c`, if `c` declares it:
its errors are the site's, the methods it enters are not part of the outcome (as `ProbeLog` mutes
them). With `init = none`, constructors are not run. -/
def initWith (run : Cur C → Option C → Site C N D → M C N D (List C)) (init : Option (N × D))
    (c : C) : M C N D Unit :=
  match init with
  | none => pure ()
  | some (n, d) => do
    if (← askMethod c n d).isSome then discard <| enter run c n d (some c)

/-- Run a site with `k` levels of method entry left; entering a method with a nonempty body at the
end of the fuel is `outOfFuel`. -/
def runK (init : Option (N × D)) : Nat → Cur C → Option C → Site C N D → M C N D (List C)
  | 0 => let stop := fun _ _ _ => throw .outOfFuel
         runSiteWith (enter stop) (initWith stop init)
  | k + 1 => runSiteWith (enter (runK init k)) (initWith (runK init k) init)

def runSite (init : Option (N × D)) : Site C N D → M C N D (List C) := runK init fuel none none

/-- A client: the classes it loads, then the sites it executes, in order. With `init`, the name and
descriptor of the no-argument constructor, an instance a site creates runs its constructor's body
(`initWith`); without, constructors are not run (the `Jvm` catalogue's classes have empty ones). -/
structure Program (C N D : Type) where
  loads : List C := []
  sites : List (Site C N D) := []
  init : Option (N × D) := none
  deriving Repr

def link (p : Program C N D) : M C N D (List C) := do
  for x in p.loads do load x
  pure (← p.sites.mapM (runSite p.init)).flatten

/-- The outcome of linking `p` in `w`: the first error, or the sequence of methods entered, in order
(Track J4). A site that enters no method contributes the class whose field it accesses or that it
instantiates; with empty bodies, the sequence is the class each site ran. -/
def outcome (w : World C N D) (p : Program C N D) : Except LinkError (List C) :=
  (link p).run.run (answer w)

/-- The linkage footprint: every entry of the class table linking `p` read. -/
def footprint (w : World C N D) (p : Program C N D) : List (Q C N D) :=
  (link p).run.trace (answer w)

/-- **T1 for linkage.** An edited class table that agrees with the old one on a client's footprint
links the client the same way. -/
theorem link_congr (w w' : World C N D) (p : Program C N D)
    (h : ∀ q ∈ footprint w p, answer w q = answer w' q) : outcome w p = outcome w' p :=
  Query.Task.run_congr _ _ _ h

/-- MiMa's question for one client: an edit is *linkage-compatible* for `p` if `p` still links
whenever it did. Agreement on the footprint is sufficient (`link_congr`), not necessary: adding a
method changes the answer to a query and leaves the client linking. -/
def Compatible (w₀ w₁ : World C N D) (p : Program C N D) : Prop :=
  (outcome w₀ p).toBool = true → (outcome w₁ p).toBool = true

/-- *Same behaviour*: `p` has the same outcome against both tables, the same error or the same
methods entered in the same order. An edit that is compatible for `p` but not same-behaviour links
and runs different code (`Jvm.Clients.changesSomeClient`). -/
def SameBehaviour (w₀ w₁ : World C N D) (p : Program C N D) : Prop :=
  outcome w₀ p = outcome w₁ p

instance (w₀ w₁ : World C N D) (p : Program C N D) : Decidable (SameBehaviour w₀ w₁ p) :=
  inferInstanceAs (Decidable (outcome w₀ p = outcome w₁ p))

theorem compatible_of_footprint (w₀ w₁ : World C N D) (p : Program C N D)
    (h : ∀ q ∈ footprint w₀ p, answer w₀ q = answer w₁ q) : Compatible w₀ w₁ p := by
  intro h0; rwa [← link_congr w₀ w₁ p h]

end Jvm
