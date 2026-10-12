import Query.Task
import Jvm.Link
import ScalaTypes.Resolve
import ScalaTypes.Desugar
/-!
# Lowering a Scala subset to classfiles, as a `Task`

Lowering a unit reads other definitions' interfaces (`Q.decl`), which is what scalac reads from
pickles or TASTy: an ancestor's members for linearization, mixin forwarders and bridges, a value
class's underlying type for erasure. So a unit's lowering has a trace, and T1 (`lower_congr`)
says an environment that agrees on it gives the same classfiles.

The output is a `Jvm.Classfile` (`ClassOut.toJvm`) plus what `Jvm` does not model yet: fields,
access, `ACC_BRIDGE`, and the invoke instructions of synthesized bodies (forwarders, bridges,
`$init$` calls). Those are compared with scalac's classfiles by the calibration probe
(`packages/scala/probes`).

The rules are scalac 2.13's; where 2.12 or Scala 3 differs, the code branches on `Dialect` and says so.
-/

open Query

namespace Scala

/-! ## Erasure -/

def jname (n : String) : String := s!"L{n};"

/-- Erasure of a type in a descriptor. A value class erases to its underlying type, which needs
its declaration. -/
def erase : Ty → M String
  | .int => pure "I"
  | .bool => pure "Z"
  | .unit => pure "V"
  | .str => pure "Ljava/lang/String;"
  | .obj | .any | .tp .. => pure "Ljava/lang/Object;"
  | .this c => pure (jname (c.headD ""))
  | .arr d => pure s!"[{jname d}"
  | .opq _ r => erase r
  | .ref n => do
    -- a library class outside the prelude erases to itself
    let some v ← askDecl n false | pure (jname n)
    let d := v.decl
    match d.kind, d.under with
    | .vcls, some (_, .int) => pure "I"
    | .vcls, some (_, .str) => pure "Ljava/lang/String;"
    | .vcls, some _ => pure "Ljava/lang/Object;"
    | _, _ => pure (jname n)

/-- Erasure as a parameter: `Unit` is boxed. -/
def eraseP (t : Ty) : M String := do
  let e ← erase t
  pure (if e == "V" then "Lscala/runtime/BoxedUnit;" else e)

def descOf (pre : List String) (ps : List Ty) (r : Ty) : M String := do
  let ps ← ps.mapM eraseP
  pure s!"({String.join (pre ++ ps)}){← erase r}"

/-- The descriptor of a member as declared in its owner. -/
def Mem.desc (m : Mem) : M String := descOf [] m.allParams m.res

/-! ## Output -/

structure Insn where
  op : String
  owner : String
  name : String
  desc : String
  deriving DecidableEq, Repr

structure MOut where
  name : String
  desc : String
  static : Bool := false
  abs : Bool := false
  final : Bool := false
  priv : Bool := false
  bridge : Bool := false
  /-- A trait field's setter, `T$_setter_$v_$eq`. -/
  setter : Bool := false
  /-- The invokes of a synthesized body; `none` for a user body, which is not compared. For a
  constructor, only its `$init$` calls. -/
  calls : Option (List Insn) := none
  deriving DecidableEq, Repr

structure FOut where
  name : String
  desc : String
  static : Bool := false
  final : Bool := false
  priv : Bool := true
  deriving DecidableEq, Repr

structure ClassOut where
  name : String
  itf : Bool := false
  abs : Bool := false
  final : Bool := false
  super : Option String := none
  ifaces : List String := []
  methods : List MOut := []
  fields : List FOut := []
  /-- Only part of the classfile is modelled (a class implementing a trait's `lazy val`); the
  probe compares only what is listed. -/
  partly : Bool := false
  /-- `InnerClasses` entries: inner class, outer class, simple name, flags. Not part of linkage. -/
  inner : List (String × String × String × List String) := []
  deriving DecidableEq, Repr

def ClassOut.toJvm (c : ClassOut) : Jvm.Classfile String String String where
  header := { isInterface := c.itf, isAbstract := c.abs, isFinal := c.final, super := c.super,
              ifaces := c.ifaces }
  methods := c.methods.map fun m =>
    (m.name, m.desc, { isStatic := m.static, isAbstract := m.abs, isFinal := m.final,
                       access := if m.priv then .priv else .pub })
  fields := c.fields.map fun f =>
    (f.name, f.desc, { isStatic := f.static, isFinal := f.final, access := if f.priv then .priv else .pub })

def toWorld (cs : List ClassOut) : Jvm.World String String String :=
  fun n => (cs.find? (·.name == n)).map ClassOut.toJvm

/-! ## Lowering -/

def setterName (t : String) (v : String) : String := s!"{t}$_setter_${v}_$eq"

/-- Does a trait have an initialiser `$init$`, and do its subclasses' constructors call it? Scala
2: unless the trait is an interface (no concrete member). Scala 3: if it has a statement or a field
to initialise; here, a concrete `val`. Also, *when the trait is compiled in the same run*, if it has
a `lazy val` or an extension method (even an abstract one). Read from TASTy, such a trait has
`NoInits`, so a subclass compiled apart from it does not call the `$init$` the trait has (F6 in
`docs/status.md`; the extension case is new). -/
def hasInit (dl : Dialect) (inRun : Bool) (t : Decl) : Bool :=
  match dl with
  | .s212 | .s213 => t.members.any (!·.abs)
  | .s3 => t.members.any fun m =>
    (m.isVal && !m.abs && !m.lzy) || (inRun && (m.lzy || m.ext.isSome))

/-- The classfile's interfaces: the direct trait parents, minus those another direct parent
already extends. -/
def ifacesOf (d : Decl) : M (List String) := do
  let ps ← d.parents.mapM fun (p, _) => do pure (p, ← lin fuel (← need p))
  pure (d.traits.map (·.1) |>.filter fun t =>
    !ps.any fun (p, l) => p != t && l.any (·.1.name == t))


/-- Add `m` unless a method of the same name and descriptor is already there. -/
def addM (ms : List MOut) (m : MOut) : List MOut :=
  if ms.any fun x => x.name == m.name && x.desc == m.desc then ms else ms ++ [m]

def ctorName : String := "<init>"

/-- A value class: its name, field and erased underlying type. -/
def vclsOf (t : Ty) : M (Option (String × String × String)) := do
  match t with
  | .ref n =>
    let d ← need n
    match d.kind, d.under with
    | .vcls, some (x, u) => pure (some (n, x, ← erase u))
    | _, _ => pure none
  | _ => pure none

/-- Bridges in class `d`: for each method `d` defines (its own and its mixin forwarders), an
ancestor's member it overrides (`overridesIn`, by `memberType`) whose erasure differs, unless the
superclass already pairs the two. -/
def bridges (self : String) (l : List Anc) (sup : List Anc) (ms : List MOut) :
    M (List MOut) := do
  let mut out := ms
  for g in sigGroups self l do
    let some ((o, _), m) := winner g | continue
    if m.abs then continue
    let n := m.name
    let e ← m.desc
    for ((a, _), m') in g do
      if a.name == o.name then continue
      let e' ← m'.desc
      if e' == e then continue
      if sup.any (·.1.name == o.name) && sup.any (·.1.name == a.name) then continue
      -- a value class in the target's signature is unboxed (argument) or boxed (result)
      let unbox ← m.allParams.filterMapM vclsOf
      let box ← (vclsOf m.res)
      let call : Insn := ⟨"invokevirtual", self, n, e⟩
      let calls : List Insn := unbox.map (fun (v, x, u) => ⟨"invokevirtual", v, x, s!"(){u}"⟩) ++ [call] ++
        box.toList.map fun (v, _, u) => ⟨"invokespecial", v, ctorName, s!"({u})V"⟩
      out := addM out { name := n, desc := e', bridge := true, calls := some calls }
  pure out

/-- Members of a class, object or value class body: its own members and, for each trait it mixes
in, forwarders to the trait's concrete methods and implementations of the trait's fields. Fields of an
object are static from 2.13 on; a trait's field implemented in a class is final in 2.12 only. -/
def classBody (dl : Dialect) (d : Decl) (isObj : Bool) (l : List Anc) :
    M (List MOut × List FOut × List Anc) := do
  let mut ms : List MOut := []
  let mut fs : List FOut := []
  for m in d.members do
    if m.static then continue
    if !retained d.name l ((d, []), m) then continue
    if m.fieldOnly then
      fs := fs ++ [{ name := m.name, desc := ← erase m.res, static := isObj && dl != .s212, final := true, priv := m.priv }]
      continue
    let e ← m.desc
    if m.isVal && !m.abs then
      fs := fs ++ [{ name := m.name, desc := ← erase m.res, static := isObj && dl != .s212, final := true }]
    ms := addM ms { name := m.name, desc := e, abs := m.abs, final := m.final, priv := m.priv }
  let mx ← mixins d l
  for (t, _) in mx do
    for m in t.members do
      -- (a trait's retained inline method is not mixed in here: not in the spaces)
      if m.lzy || m.inline then continue
      let some ((o, _), w) := lookupSig d.name l ((t, []), m) | continue
      if o.name != t.name || w.abs then continue
      let e ← m.desc
      if m.isVal then
        fs := fs ++ [{ name := m.name, desc := ← erase m.res, static := isObj && dl != .s212, final := dl == .s212 }]
        ms := addM ms { name := m.name, desc := e }
        ms := addM ms { name := setterName t.name m.name, desc := s!"({← erase m.res})V", setter := true }
      else
        let sd ← descOf [jname t.name] m.allParams m.res
        let call : Insn := ⟨"invokestatic", t.name, m.name ++ "$", sd⟩
        ms := addM ms { name := m.name, desc := e, final := m.final, calls := some [call] }
  pure (ms, fs, mx)

/-- The `$init$` calls of a constructor: the mixed-in traits, base first. -/
def initCalls (dl : Dialect) (mx : List Anc) : M (List Insn) := do
  let ts ← mx.reverse.filterM fun (t, _) => do pure (hasInit dl (← needView t.name).inRun t)
  pure <| ts.map fun (t, _) => ⟨"invokestatic", t.name, "$init$", s!"({jname t.name})V"⟩

/-- Does `d` implement a trait's `lazy val`? Its classfile is then only partly modelled. -/
def implementsLazy (mx : List Anc) : Bool := mx.any fun (t, _) => t.members.any (·.lzy)

/-- The accessor of an inner class's outer instance, `Outer$Inner$$$outer`. -/
def outerAccessor (cls : String) : String := cls ++ "$$$outer"

def lowerTrait (dl : Dialect) (d : Decl) (outer : Option String := none) : M ClassOut := do
  -- an inner trait declares its outer accessor, which implementing classes define
  let mut ms : List MOut :=
    (outer.toList.map fun o => { name := outerAccessor d.name, desc := s!"(){jname o}", abs := true })
  let l ← lin fuel d
  for m in d.members do
    if !retained d.name l ((d, []), m) then continue
    let e ← m.desc
    if m.isVal && !m.lzy then
      ms := ms ++ [{ name := m.name, desc := e, abs := true }]
      if !m.abs then
        ms := ms ++ [{ name := setterName d.name m.name, desc := s!"({← erase m.res})V", abs := true }]
    else if m.abs then
      ms := ms ++ [{ name := m.name, desc := e, abs := true }]
    else
      ms := ms ++ [{ name := m.name, desc := e },
                   { name := m.name ++ "$", desc := ← descOf [jname d.name] m.allParams m.res, static := true,
                     calls := some [⟨"invokespecial", d.name, m.name, e⟩] }]
  if hasInit dl true d then
    ms := ms ++ [{ name := "$init$", desc := s!"({jname d.name})V", static := true }]
  pure { name := d.name, itf := true, abs := true, ifaces := ← ifacesOf d, methods := ms }

def superLin (d : Decl) : M (List Anc) := do
  match d.super with
  | none => pure []
  | some (s, _) => lin fuel (← need s)

/-- An inner class (nested in a class or trait, `outer`) holds its outer instance: a field `$outer`
(public in Scala 2, private in Scala 3), an accessor (`final` in Scala 3), and a constructor
parameter before the others. -/
def lowerClass (dl : Dialect) (d : Decl) (outer : Option String := none) : M ClassOut := do
  let l ← lin fuel d
  let (ms, fs, mx) ← classBody dl d false l
  let (ms, fs) : List MOut × List FOut := match outer with
    | some o => (ms ++ [({ name := outerAccessor d.name, desc := s!"(){jname o}", final := dl == .s3 } : MOut)],
                 fs ++ [({ name := "$outer", desc := jname o, final := true, priv := dl == .s3 } : FOut)])
    | none => (ms, fs)
  let cps ← d.ctor.mapM eraseP
  let ctor : MOut := { name := ctorName, desc := s!"({String.join (outer.toList.map jname ++ cps)})V",
                       calls := some (← initCalls dl mx) }
  let ms ← bridges d.name l (← superLin d) (ms ++ [ctor])
  let part := implementsLazy mx
  pure { name := d.name, abs := d.abs, final := d.final, super := d.super.map (·.1),
         ifaces := ← ifacesOf d, methods := if part then [ctor] else ms, fields := if part then [] else fs,
         partly := part }

def moduleName (n : String) : String := n ++ "$"

/-- A value class: the underlying field and its getter, each method forwarding to its extension
method in the companion, and `hashCode`/`equals` likewise. -/
def lowerVcls (d : Decl) : M ClassOut := do
  let some (x, u) := d.under | throw "value class without parameter"
  let eu ← erase u
  let mod := moduleName d.name
  let get : Insn := ⟨"getstatic", mod, "MODULE$", jname mod⟩
  let getx : Insn := ⟨"invokevirtual", d.name, x, s!"(){eu}"⟩
  let mut ms : List MOut := [{ name := x, desc := s!"(){eu}" }]
  let exts : List (String × List Ty × Ty) :=
    (d.members.filter fun m => !m.isVal).map fun m => (m.name, m.params, m.res)
  for (n, ps, r) in exts ++ [("hashCode", [], .int), ("equals", [.obj], .bool)] do
    let r' ← erase r
    let e := s!"({String.join (← ps.mapM eraseP)}){r'}"
    let ee := s!"({eu}{String.join (← ps.mapM eraseP)}){r'}"
    ms := ms ++ [{ name := n, desc := e, calls := some [get, getx, ⟨"invokevirtual", mod, n ++ "$extension", ee⟩] }]
  ms := ms ++ [{ name := ctorName, desc := s!"({eu})V", calls := some [] }]
  pure { name := d.name, final := true, ifaces := ← ifacesOf d, methods := ms,
         fields := [{ name := x, desc := eu, final := true }] }

/-- The extension methods a value class's companion gets. -/
def extensions (d : Decl) : M (List MOut) := do
  let some (_, u) := d.under | pure []
  let eu ← erase u
  let exts : List (String × List Ty × Ty) :=
    (d.members.filter fun m => !m.isVal).map fun m => (m.name, m.params, m.res)
  let all : List (String × List Ty × Ty) := exts ++ [("hashCode", [], .int), ("equals", [.obj], .bool)]
  all.mapM fun (n, ps, r) => do
    let r' ← erase r
    pure ({ name := n ++ "$extension", desc := s!"({eu}{String.join (← ps.mapM eraseP)}){r'}", final := true } : MOut)

/-- An object nested in an object: its module class has a public constructor, and is final only in
Scala 3. -/
def lowerObject (dl : Dialect) (d : Decl) (vc : Option Decl) (nested : Bool := false) : M ClassOut := do
  let self := moduleName d.name
  let l ← lin fuel d
  let (ms, fs, mx) ← classBody dl d true l
  let ms ← bridges self l (← superLin d) ms
  let ms := ms ++ (← match vc with | some v => extensions v | none => pure [])
  let serialBase := l.any fun (a, _) => a.name == "java/io/Serializable" || a.name == "scala/Serializable"
  -- 2.12 initialises an object in its constructor, later versions in its static initialiser
  let inits ← initCalls dl mx
  let extra : List MOut :=
    [{ name := ctorName, desc := "()V", priv := !nested, calls := some (if dl == .s212 then inits else []) },
     { name := "<clinit>", desc := "()V", static := true, calls := some (if dl == .s212 then [] else inits) }] ++
    -- a serializable object resolves to its module instance: `readResolve` in 2.12, `writeReplace`
    -- later; Scala 3 makes every object serializable
    (if dl == .s3 || (dl == .s213 && serialBase) then
      [{ name := "writeReplace", desc := "()Ljava/lang/Object;", priv := true }]
     else if dl == .s212 && serialBase then
      [{ name := "readResolve", desc := "()Ljava/lang/Object;", priv := true }]
     else [])
  let ser := if dl == .s3 && !serialBase then ["java/io/Serializable"] else []
  let part := implementsLazy mx
  pure { name := self, final := !nested || dl == .s3, super := d.super.map (·.1), ifaces := (← ifacesOf d) ++ ser,
         -- (Scala 3's static initialiser of an object with a lazy val is private)
         methods := if part then (extra.take 2).map (fun m =>
             if m.name == "<clinit>" && dl == .s3 then { m with priv := true } else m)
           else ms ++ extra,
         fields := (if part then [] else [{ name := "MODULE$", desc := jname self, static := true, final := dl != .s212, priv := false }] ++ fs),
         partly := part }

/-- Static forwarders in the companion class (or a mirror class) for the object's public methods,
its own and inherited, except those whose name the companion class also has. Scala 2 skips
trait setters and bridges; Scala 3 forwards setters, and some bridges. -/
def forwarders (dl : Dialect) (od : Decl) (o : ClassOut) (clsNames : List String) : M (List MOut) := do
  let l ← lin fuel od
  let mut cands := o.methods.filter fun m =>
    !m.static && !m.priv && !m.abs && !m.bridge && m.name != ctorName &&
    !(dl != .s3 && m.setter)
  -- Scala 3 forwards a bridge too, when the member of that erased signature found first along
  -- the linearization is concrete: dotc looks members up by signature, and skips deferred ones.
  if dl == .s3 then
    for b in o.methods.filter (·.bridge) do
      let sameSig ← (hitsAbove l b.name).filterM fun (_, m) => do pure ((← m.desc) == b.desc)
      let concrete := match sameSig with
        | (_, m) :: _ => !m.abs
        | [] => false
      if concrete then cands := cands ++ [b]
  for g in sigGroups od.name l do
    let some ((w, _), m) := winner g | continue
    let n := m.name
    let e ← m.desc
    if m.abs || m.static || m.priv || !retained w.name l ((w, []), m) ||
       cands.any (fun c => c.name == n && c.desc == e) then continue
    cands := cands ++ [{ name := n, desc := e }]
    if dl == .s3 && m.isVal && !m.lzy then
      cands := cands ++ [{ name := setterName w.name n, desc := s!"({← erase m.res})V" }]
  pure <| (cands.filter fun m => !clsNames.contains m.name).map fun m =>
    { name := m.name, desc := m.desc, static := true,
      calls := some [⟨"getstatic", o.name, "MODULE$", jname o.name⟩, ⟨"invokevirtual", o.name, m.name, m.desc⟩] }

/-- Scala 3 `@static` members of an object move to its companion class: a method, or a field
initialised in the class's static initialiser (which is private). -/
def statics (od : Decl) : M (List MOut × List FOut) := do
  let ss := od.members.filter (·.static)
  let ms ← (ss.filter (!·.isVal)).mapM fun m => do pure ({ name := m.name, desc := ← m.desc, static := true } : MOut)
  let fs ← (ss.filter (·.isVal)).mapM fun m => do
    pure ({ name := m.name, desc := ← erase m.res, static := true, final := true, priv := false } : FOut)
  let clinit : List MOut := if fs.isEmpty then [] else [{ name := "<clinit>", desc := "()V", static := true, priv := true }]
  pure (ms ++ clinit, fs)

def lowerSrc (dl : Dialect) (s : Src) : M (List ClassOut) := do
  let innerOf := if s.inObj then none else s.outer
  let c ← match s.cls with
    | none => pure none
    | some d => match d.kind with
      | .trt => some <$> lowerTrait dl d innerOf
      | .vcls => some <$> lowerVcls d
      | _ => some <$> lowerClass dl d innerOf
  let vc := s.cls.filter (·.kind == .vcls)
  match s.obj with
  | some od =>
    let o ← lowerObject dl od vc (s.outer.isSome && s.inObj)
    match c with
    | some c =>
      let clsNames := (← match s.cls with
        | some d => do pure (memberNames (← lin fuel d))
        | none => pure []) ++ c.methods.map (·.name)
      let fw ← forwarders dl od o clsNames
      let (sm, sf) ← statics od
      pure [{ c with methods := c.methods ++ sm ++ fw.filter (fun f =>
                !c.methods.any fun m => m.name == f.name && m.desc == f.desc),
                     fields := c.fields ++ sf }, o]
    | none =>
      -- only a top-level object gets a mirror class of static forwarders
      if s.outer.isSome then pure [o] else
      let (sm, sf) ← statics od
      pure [{ name := s.name, final := true, methods := sm ++ (← forwarders dl od o []), fields := sf }, o]
  | none =>
    match vc, c with
    | some v, some c => do
      -- a value class always has a companion
      let od : Decl := { name := v.name, kind := .obj }
      let o ← lowerObject dl od vc
      pure [{ c with methods := c.methods ++ (← forwarders dl od o (c.methods.map (·.name))) }, o]
    | _, _ => pure c.toList

/-- Lower a unit against an environment of interfaces. -/
def lower (dl : Dialect) (s : Src) (env : (q : Q) → Ans q) : Except String (List ClassOut) :=
  (lowerSrc dl s).run.run env

def trace (dl : Dialect) (s : Src) (env : (q : Q) → Ans q) : List Q :=
  (lowerSrc dl s).run.trace env

/-- **T1 for lowering.** An environment that agrees on a unit's trace lowers it to the same
classfiles. -/
theorem lower_congr (dl : Dialect) (s : Src) (e e' : (q : Q) → Ans q)
    (h : ∀ q ∈ trace dl s e, e q = e' q) : lower dl s e = lower dl s e' :=
  (Query.Task.run_eq_of_trace _ e e' h).1

/-- What nesting adds to the classfiles of a program, which `lowerSrc` cannot see unit by unit:
`InnerClasses` entries (a nested class's own, and its unit's nested members in the class or
mirror class, and in Scala 3 also in the module class), and in Scala 3 a static field in a module
class for each object nested in it. -/
def nesting (dl : Dialect) (q : Program) (cs : List ClassOut) : List ClassOut :=
  let entry (n : Src) : List (String × String × String × List String) :=
    match n.outer, n.anonIn with
    | none, some _ => [(n.name, "", "", ["public", "static", "final"])]
    | none, none => []
    | some o, _ =>
      let fl (obj : Bool) := ["public"] ++ (if n.inObj then ["static"] else []) ++
        (if (obj && dl == .s3) || (!obj && (n.cls.map (·.final)).getD false) then ["final"] else []) ++
        (if (n.cls.map (·.kind == .trt)).getD false && !obj then ["interface", "abstract"] else [])
      (n.cls.toList.map fun _ => (n.name, o, n.simple, fl false)) ++
      (n.obj.toList.map fun _ => (n.name ++ "$", o, n.simple ++ "$", fl true))
  let membersOf (u : String) (inObjOnly : Bool) : List Src :=
    q.filter fun n => n.outer == some u && (n.inObj || !inObjOnly)
  let anonsOf (u : String) : List Src := q.filter fun n => n.anonIn == some u
  cs.map fun c =>
    -- which unit is `c` the class part (or mirror) of, or the module class of?
    let asCls := q.find? fun u => u.name == c.name
    let asMod := q.find? fun u => u.name ++ "$" == c.name && u.obj.isSome
    -- a nested class and its companion module list both their entries
    let own := match asCls, asMod with
      | some u, _ => if u.cls.isSome || u.obj.isNone then entry u else []
      | _, some u => entry u
      | _, _ => []
    let members := match asCls, asMod with
      | some u, _ => (membersOf u.name false).flatMap entry
      | _, some u => if dl == .s3 then (membersOf u.name true ++ anonsOf u.name).flatMap entry else []
      | _, _ => []
    let fields := match asMod with
      | some u => if dl == .s3 then (membersOf u.name true).filter (·.obj.isSome) |>.map fun n =>
          ({ name := n.simple, desc := jname (n.name ++ "$"), static := true, final := true, priv := false } : FOut)
        else []
      | none => []
    { c with inner := own ++ members, fields := c.fields ++ fields }

/-- Lower a program: desugared, against the prelude and its own definitions. -/
def lowerProgram (dl : Dialect) (p : Program) : Except String (List ClassOut) := do
  let q := p.desugar dl
  let env := (prelude dl ++ q).env
  let cs ← q.mapM fun s => lower dl s env
  pure (nesting dl q cs.flatten)

/-- The prelude's own classfiles: the standard library a client links against. -/
def preludeClasses (dl : Dialect) : Except String (List ClassOut) := do
  let cs ← (prelude dl).mapM fun s => lower dl s (prelude dl).env
  pure cs.flatten

/-- Separate compilation: the units `lib` in one run, then the rest in a second run that reads
`lib` from the classpath. -/
def lowerSeparately (dl : Dialect) (p : Program) (lib : List String) : Except String (List ClassOut) := do
  let cs ← p.mapM fun s =>
    if lib.contains s.name then lower dl s (p.envIn lib) else lower dl s (p.envIn (p.map (·.name) |>.filter (!lib.contains ·)))
  pure cs.flatten

end Scala
