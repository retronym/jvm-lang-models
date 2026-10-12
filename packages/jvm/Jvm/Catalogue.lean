import Jvm.Link
/-!
# A catalogue of library edits, linked

Each case is a library edit (`v0` → `v1`) and a client compiled against `v0`. The client's
classes and sites are fixed; only the library's classfiles change. Each case states the outcome
before and after, by kernel `decide` (no `native_decide`), and names the MiMa problem that reports it where there is one.
`lake exe jvmcases` dumps the cases; `packages/jvm/probes` renders them to classfiles and checks the outcomes on
HotSpot.

Classes: `A`, `B` (library classes), `I`, `J` (library interfaces), `X` (the client's class); the
calibration spaces of `Clients.lean` also use `K` (a third interface) and `Y` (a second client class).
`O` is `java.lang.Object`, in the class tables that need it (`object`).
-/

namespace Jvm.Catalogue

inductive C | A | B | I | J | X | K | Y | O
  deriving DecidableEq, Repr

/-- `init` is `<init>`, a constructor; `hashCode` and `finalize` are `Object`'s; `run` is a library
method whose body calls `m` (Track J4). -/
inductive N | m | init | hashCode | finalize | run
  deriving DecidableEq, Repr

/-- `v` is `()V`, `i` is `()I`; `s` is a field of type `String`; `iv` is `(I)V`. -/
inductive D | v | i | s | iv
  deriving DecidableEq, Repr

abbrev W := World C N D
abbrev P := Program C N D

def world (l : List (C × Classfile C N D)) : W := fun c => (l.find? (·.1 = c)).map (·.2)

def inst : MethodInfo C N D := {}
def abs : MethodInfo C N D := { isAbstract := true }

structure Case where
  name : String
  /-- The MiMa problem that reports the edit, if any. -/
  mima : Option String
  v0 : List (C × Classfile C N D)
  v1 : List (C × Classfile C N D)
  client : List (C × Classfile C N D) := []
  prog : P

def Case.w0 (k : Case) : W := world (k.client ++ k.v0)
def Case.w1 (k : Case) : W := world (k.client ++ k.v1)
def Case.before (k : Case) := outcome k.w0 k.prog
def Case.after (k : Case) := outcome k.w1 k.prog

open Site

def methodRemoved : Case where
  name := "methodRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, {})]
  prog := { sites := [invokevirtual .A .m .v .A] }

def resultTypeChanged : Case where
  name := "resultTypeChanged"
  mima := some "IncompatibleResultTypeProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .i, inst)] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

/-- `A` becomes an interface that `B` implements; the client's `A a = new B(); a.m()` still
verifies (an interface target is assignable) and fails to resolve `A.m` as a class method. -/
def classBecomesInterface : Case where
  name := "classBecomesInterface"
  mima := some "IncompatibleTemplateDefProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.B, { header := { super := none, ifaces := [.A] } })]
  prog := { sites := [invokevirtual .A .m .v .B] }

def becomesStatic : Case where
  name := "becomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { isStatic := true })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def becomesAbstract : Case where
  name := "becomesAbstract"
  mima := some "AbstractClassProblem"
  v0 := [(.A, {})]
  v1 := [(.A, { header := { isAbstract := true } })]
  prog := { sites := [new .A] }

def becomesFinal : Case where
  name := "becomesFinal"
  mima := some "FinalClassProblem"
  v0 := [(.A, {})]
  v1 := [(.A, { header := { isFinal := true } })]
  client := [(.X, { header := { super := some .A } })]
  prog := { loads := [.X] }

def methodBecomesFinal : Case where
  name := "methodBecomesFinal"
  mima := some "FinalMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { isFinal := true })] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  prog := { loads := [.X] }

def superclassRemoved : Case where
  name := "superclassRemoved"
  mima := some "MissingTypesProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, {})]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-- A default method becomes abstract; the client's class implements the interface and never
declared the method, so a call through the interface finds nothing to run. -/
def defaultRemoved : Case where
  name := "defaultRemoved"
  mima := some "DirectAbstractMethodProblem"
  v0 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { loads := [.X], sites := [invokeinterface .I .m .v .X] }

/-- A second interface of the client's class gains a default method of the same signature: two
maximally-specific non-abstract methods. -/
def defaultConflict : Case where
  name := "defaultConflict"
  mima := none
  v0 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.J, { header := { isInterface := true } })]
  v1 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.J, { header := { isInterface := true }, methods := [(.m, .v, inst)] })]
  client := [(.X, { header := { ifaces := [.I, .J] } })]
  prog := { loads := [.X], sites := [invokeinterface .I .m .v .X] }

/-- An override added to a subclass: still links, and the call now runs `B.m`. Compatible, but
not footprint-equal. -/
def overrideAdded : Case where
  name := "overrideAdded"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }),
         (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-- A method moves up from `B` to its superclass: links, the same code runs from a new owner. -/
def pulledUp : Case where
  name := "pulledUp"
  mima := none
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-! ## Track J3: access, `invokespecial` and private methods, interface statics, fields

Packages: `pkg := 1` is `p1`; a site without `within` runs from a class of its own in the unnamed
package. -/

def p1 : Header C := { pkg := 1 }
def iface : Header C := { isInterface := true }

def methodBecomesPrivate : Case where
  name := "methodBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { access := .priv })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def methodBecomesPackagePrivate : Case where
  name := "methodBecomesPackagePrivate"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def classBecomesPackagePrivate : Case where
  name := "classBecomesPackagePrivate"
  mima := some "InaccessibleClassProblem"
  v0 := [(.A, { header := p1 })]
  v1 := [(.A, { header := { p1 with isPublic := false } })]
  prog := { sites := [new .A] }

/-- `public` to `protected`, called from a class that is not a subclass. -/
def methodBecomesProtected : Case where
  name := "methodBecomesProtected"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

/-- The same edit, called from a subclass on itself: still links. -/
def methodBecomesProtectedSub : Case where
  name := "methodBecomesProtectedSub"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  client := [(.X, { header := { super := some .A } })]
  prog := { sites := [within .X (invokevirtual .X .m .v .X)] }

/-- The same edit, called from a subclass on an `A` that is not an `X`: §5.4.4 allows it, but the
verifier's protected check (§4.10.1.8) rejects the client. -/
def methodBecomesProtectedOther : Case where
  name := "methodBecomesProtectedOther"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  client := [(.X, { header := { super := some .A } })]
  prog := { sites := [within .X (invokevirtual .A .m .v .A)] }

/-- `A.m` becomes package-private; the client's override `X.m` in another package stops overriding
it, so a call from `A`'s package runs `A.m`: links, runs different code. -/
def overrideCutByPackage : Case where
  name := "overrideCutByPackage"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .v, inst)] }), (.B, { header := p1 })]
  prog := { sites := [within .B (invokevirtual .A .m .v .X)] }

/-- An override becomes private: a private method does not override, so `A.m` runs. A client
calling `B.m` itself breaks instead (`Jvm.Clients`): resolution finds the private `B.m` first. -/
def overrideBecomesPrivate : Case where
  name := "overrideBecomesPrivate"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }),
         (.B, { header := { super := some .A }, methods := [(.m, .v, { access := .priv })] })]
  prog := { sites := [invokevirtual .A .m .v .B] }

/-- `super.m()` from `X extends B extends A` is `invokespecial B.m`; `m` moves from `B` up to `A`. -/
def superCallPulledUp : Case where
  name := "superCallPulledUp"
  mima := none
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  client := [(.X, { header := { super := some .B } })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

def superCallRemoved : Case where
  name := "superCallRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, {}), (.B, { header := { super := some .A } })]
  client := [(.X, { header := { super := some .B } })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

def superCallAbstract : Case where
  name := "superCallAbstract"
  mima := some "AbstractClassProblem"
  v0 := [(.B, { methods := [(.m, .v, inst)] })]
  v1 := [(.B, { header := { isAbstract := true }, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { super := some .B }, methods := [(.m, .v, inst)] })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

/-- `I.super.m()` from `X implements I`, and the default becomes abstract. -/
def defaultSuperCallAbstract : Case where
  name := "defaultSuperCallAbstract"
  mima := some "DirectAbstractMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { ifaces := [.I] }, methods := [(.m, .v, inst)] })]
  prog := { sites := [within .X (invokespecial .I .m .v true)] }

def staticIfaceMethodRemoved : Case where
  name := "staticIfaceMethodRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] })]
  v1 := [(.I, { header := iface })]
  prog := { sites := [invokestaticIface .I .m .v] }

/-- A static method moves from a class to an interface it implements: interface statics are not
inherited. -/
def staticMovedToIface : Case where
  name := "staticMovedToIface"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, { isStatic := true })] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] }),
         (.A, { header := { ifaces := [.I] } })]
  prog := { sites := [invokestatic .A .m .v] }

def defaultBecomesStatic : Case where
  name := "defaultBecomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .m .v .X] }

def defaultBecomesPrivate : Case where
  name := "defaultBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { access := .priv })] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .m .v .X] }

def fld : FieldInfo := {}
def sfld : FieldInfo := { isStatic := true }

def fieldRemoved : Case where
  name := "fieldRemoved"
  mima := some "MissingFieldProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, {})]
  prog := { sites := [getfield .A .m .s .A] }

def fieldBecomesStatic : Case where
  name := "fieldBecomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, sfld)] })]
  prog := { sites := [getfield .A .m .s .A] }

def fieldBecomesFinal : Case where
  name := "fieldBecomesFinal"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, { isFinal := true })] })]
  prog := { sites := [putfield .A .m .s .A] }

def fieldBecomesPrivate : Case where
  name := "fieldBecomesPrivate"
  mima := some "MissingFieldProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, { access := .priv })] })]
  prog := { sites := [getfield .A .m .s .A] }

/-- A subclass gains a field of the same name: fields do not override, and the client's `B.m` now
resolves to `B`'s. -/
def fieldShadowed : Case where
  name := "fieldShadowed"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, fld)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { fields := [(.m, .s, fld)] }),
         (.B, { header := { super := some .A }, fields := [(.m, .s, fld)] })]
  prog := { sites := [getfield .B .m .s .B] }

/-- An interface of `B` gains a static field: field resolution searches superinterfaces before the
superclass. A client writing `B.m` breaks (`Jvm.Clients`): interface fields are final. -/
def fieldIfaceBeforeSuper : Case where
  name := "fieldIfaceBeforeSuper"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, sfld)] }), (.I, { header := iface }),
         (.B, { header := { super := some .A, ifaces := [.I] } })]
  v1 := [(.A, { fields := [(.m, .s, sfld)] }),
         (.I, { header := iface, fields := [(.m, .s, { isStatic := true, isFinal := true })] }),
         (.B, { header := { super := some .A, ifaces := [.I] } })]
  prog := { sites := [getstatic .B .m .s] }

def putstaticBecomesFinal : Case where
  name := "putstaticBecomesFinal"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, sfld)] })]
  v1 := [(.A, { fields := [(.m, .s, { isStatic := true, isFinal := true })] })]
  prog := { sites := [putstatic .A .m .s] }

/-- JVMS §5.4.5's own example of transitive overriding, as an edit. In package 1, `A.m` is
package-private, `B extends A` and `I extends B` (`I` is a class here) redeclare `m`; the client's
`X extends I` in another package declares a package-private `m`, and its class `J` in package 1 calls
`A.m` on an `X`. The edit makes `B.m` public: by (b) of §5.4.5, `X.m` then overrides `A.m` through
`B.m`, so selection picks `X.m`. Until the model had (b), it still picked `I.m`; HotSpot 21, 25 and 27 pick `X.m`. -/
def transitiveOverride : Case where
  name := "transitiveOverride"
  mima := none
  v0 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] }),
         (.B, { header := { p1 with super := some .A }, methods := [(.m, .v, { access := .pkg })] }),
         (.I, { header := { p1 with super := some .B }, methods := [(.m, .v, { access := .pkg })] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] }),
         (.B, { header := { p1 with super := some .A }, methods := [(.m, .v, inst)] }),
         (.I, { header := { p1 with super := some .B }, methods := [(.m, .v, { access := .pkg })] })]
  client := [(.X, { header := { super := some .I }, methods := [(.m, .v, { access := .pkg })] }),
             (.J, { header := p1 })]
  prog := { sites := [within .J (invokevirtual .A .m .v .X)] }

/-- A final method behind a redeclaration. `A.m` is package-private in package 1; `B` in package 2
redeclares a public `m`, which does not override it; the client's `X` in package 1 extends `B`, and
its `m` overrides both `B.m` and, from `A`'s package, `A.m`. The edit makes `A.m` final, and loading
`X` fails (§5.3.5 checks every superclass's final methods, not the nearest declaration). -/
def methodBecomesFinalBehind : Case where
  name := "methodBecomesFinalBehind"
  mima := none
  v0 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] }),
         (.B, { header := { pkg := 2, super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg, isFinal := true })] }),
         (.B, { header := { pkg := 2, super := some .A }, methods := [(.m, .v, inst)] })]
  client := [(.X, { header := { p1 with super := some .B }, methods := [(.m, .v, inst)] })]
  prog := { loads := [.X] }

def j3 : List Case :=
  [methodBecomesPrivate, methodBecomesPackagePrivate, classBecomesPackagePrivate,
   methodBecomesProtected, methodBecomesProtectedSub, methodBecomesProtectedOther,
   overrideCutByPackage, overrideBecomesPrivate, superCallPulledUp, superCallRemoved,
   superCallAbstract, defaultSuperCallAbstract, staticIfaceMethodRemoved, staticMovedToIface,
   defaultBecomesStatic, defaultBecomesPrivate, fieldRemoved, fieldBecomesStatic,
   fieldBecomesFinal, fieldBecomesPrivate, fieldShadowed, fieldIfaceBeforeSuper,
   putstaticBecomesFinal, transitiveOverride, methodBecomesFinalBehind]

/-! ## Track J5: sealed classes and constructors

Every class here declares its constructors, so `packages/jvm/probes` renders exactly those (and no default
`()V`); each keeps a public `()V`, which `new` and subclasses' constructors call. -/

def ctor0 : N × D × MethodInfo C N D := (.init, .v, inst)
def ctorI (acc : Access := .pub) : N × D × MethodInfo C N D := (.init, .iv, { access := acc })

/-- A class becomes sealed without permitting the client's subclass: loading the subclass fails
(JVMS §5.3.5), with HotSpot's "cannot inherit from sealed class". -/
def classBecomesSealed : Case where
  name := "classBecomesSealed"
  mima := none
  v0 := [(.A, { methods := [ctor0] })]
  v1 := [(.A, { header := { permitted := some [.B] }, methods := [ctor0] })]
  client := [(.X, { header := { super := some .A }, methods := [ctor0] })]
  prog := { loads := [.X] }

/-- The same, permitting the client's subclass: it loads. -/
def classBecomesSealedPermitting : Case where
  name := "classBecomesSealedPermitting"
  mima := none
  v0 := [(.A, { methods := [ctor0] })]
  v1 := [(.A, { header := { permitted := some [.B, .X] }, methods := [ctor0] })]
  client := [(.X, { header := { super := some .A }, methods := [ctor0] })]
  prog := { loads := [.X] }

/-- An interface becomes sealed without permitting the client's implementation. -/
def ifaceBecomesSealed : Case where
  name := "ifaceBecomesSealed"
  mima := none
  v0 := [(.I, { header := iface })]
  v1 := [(.I, { header := { iface with permitted := some [.B] } })]
  client := [(.X, { header := { ifaces := [.I] }, methods := [ctor0] })]
  prog := { loads := [.X] }

/-- A sealed class in another package permits the client's subclass, but the subclass is not
public: §5.3.5 requires the same run-time package then. -/
def sealedPermitsNonPublicElsewhere : Case where
  name := "sealedPermitsNonPublicElsewhere"
  mima := none
  v0 := [(.A, { header := p1, methods := [ctor0] })]
  v1 := [(.A, { header := { p1 with permitted := some [.X] }, methods := [ctor0] })]
  client := [(.X, { header := { super := some .A, isPublic := false }, methods := [ctor0] })]
  prog := { loads := [.X] }

/-- The same with a public subclass: it loads. -/
def sealedPermitsPublicElsewhere : Case where
  name := "sealedPermitsPublicElsewhere"
  mima := none
  v0 := [(.A, { header := p1, methods := [ctor0] })]
  v1 := [(.A, { header := { p1 with permitted := some [.X] }, methods := [ctor0] })]
  client := [(.X, { header := { super := some .A }, methods := [ctor0] })]
  prog := { loads := [.X] }

/-- A constructor removed: `new A(0)` does not link. -/
def ctorRemoved : Case where
  name := "ctorRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [ctor0, ctorI] })]
  v1 := [(.A, { methods := [ctor0] })]
  prog := { sites := [construct .A .init .iv] }

def ctorBecomesPrivate : Case where
  name := "ctorBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [ctor0, ctorI] })]
  v1 := [(.A, { methods := [ctor0, ctorI .priv] })]
  prog := { sites := [construct .A .init .iv] }

def ctorBecomesPackagePrivate : Case where
  name := "ctorBecomesPackagePrivate"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [ctor0, ctorI] })]
  v1 := [(.A, { header := p1, methods := [ctor0, ctorI .pkg] })]
  prog := { sites := [construct .A .init .iv] }

/-- A constructor moved to the superclass: constructors are not inherited, so `new B(0)` does not
link, although resolution finds `A.<init>(I)V`. -/
def ctorPulledUp : Case where
  name := "ctorPulledUp"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [ctor0] }), (.B, { header := { super := some .A }, methods := [ctor0, ctorI] })]
  v1 := [(.A, { methods := [ctor0, ctorI] }), (.B, { header := { super := some .A }, methods := [ctor0] })]
  prog := { sites := [construct .B .init .iv] }

/-- The constructor moves up as in `ctorPulledUp`, but becomes private there. Resolution finds
`A.<init>(I)V` and its access check fails before `invokespecial`'s check that the constructor is
declared by `B` (JVMS §6.5 `invokespecial`, linking exceptions), so the error is `IllegalAccessError`
rather than `NoSuchMethodError`. -/
def ctorPulledUpPrivate : Case where
  name := "ctorPulledUpPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [ctor0] }), (.B, { header := { super := some .A }, methods := [ctor0, ctorI] })]
  v1 := [(.A, { methods := [ctor0, ctorI .priv] }), (.B, { header := { super := some .A }, methods := [ctor0] })]
  prog := { sites := [construct .B .init .iv] }

/-- The class becomes abstract: `new` fails before the constructor resolves. -/
def ctorClassBecomesAbstract : Case where
  name := "ctorClassBecomesAbstract"
  mima := some "AbstractClassProblem"
  v0 := [(.A, { methods := [ctor0, ctorI] })]
  v1 := [(.A, { header := { isAbstract := true }, methods := [ctor0, ctorI] })]
  prog := { sites := [construct .A .init .iv] }

def j5 : List Case :=
  [classBecomesSealed, classBecomesSealedPermitting, ifaceBecomesSealed,
   sealedPermitsNonPublicElsewhere, sealedPermitsPublicElsewhere, ctorRemoved, ctorBecomesPrivate,
   ctorBecomesPackagePrivate, ctorPulledUp, ctorPulledUpPrivate, ctorClassBecomesAbstract]

/-! ## Track J7: default methods along superinterface chains -/

/-- A package-private method above a default. The client's `X extends A implements I` inherits `I`'s
default `m`; `A`, in package 1 and not implementing `I`, gains a package-private `m`, which javac
accepts. `A.m` can override `I.m` (§5.4.5: `I.m` is public), so `invokeinterface I.m` selects it, and
fails: a selected method that is neither public nor private is an `IllegalAccessError` (JVMS §6.5,
`invokeinterface`). -/
def pkgMethodAboveDefault : Case where
  name := "pkgMethodAboveDefault"
  mima := none
  v0 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }), (.A, { header := p1 })]
  v1 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.A, { header := p1, methods := [(.m, .v, { access := .pkg })] })]
  client := [(.X, { header := { super := some .A, ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .m .v .X] }

def j7 : List Case := [pkgMethodAboveDefault]

/-! ## Track J8: field resolution through superinterfaces at depth -/

/-- `fieldIfaceBeforeSuper` one level down: `B extends A implements J`, and `J extends K`. `K` gains a
constant `m`; field resolution (§5.4.3.2) searches `B`'s superinterfaces recursively, so `J`'s
superinterface `K` before `B`'s superclass `A`, and `B.m` now reads `K.m` (scala-garden/mima#995). -/
def fieldIfaceDepthBeforeSuper : Case where
  name := "fieldIfaceDepthBeforeSuper"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, sfld)] }), (.K, { header := iface }),
         (.J, { header := { iface with ifaces := [.K] } }),
         (.B, { header := { super := some .A, ifaces := [.J] } })]
  v1 := [(.A, { fields := [(.m, .s, sfld)] }),
         (.K, { header := iface, fields := [(.m, .s, { isStatic := true, isFinal := true })] }),
         (.J, { header := { iface with ifaces := [.K] } }),
         (.B, { header := { super := some .A, ifaces := [.J] } })]
  prog := { sites := [getstatic .B .m .s] }

def j8 : List Case := [fieldIfaceDepthBeforeSuper]

/-! ## `Object`'s methods in interface resolution

`object` is `java.lang.Object` as far as these cases need it: a public `hashCode()I` and a protected
`finalize()V`, in a package of its own (`java.lang`; the number is the model's, the dump names it
`java.lang.Object`). An interface's superclass is `Object` (`super := some .O`), as in its classfile. -/

def object : C × Classfile C N D :=
  (.O, { header := { pkg := 9 }, methods := [(.hashCode, .i, inst), (.finalize, .v, { access := .prot })] })

def ifaceO : Header C := { isInterface := true, super := some .O }

/-- An interface drops its redeclaration of `hashCode`. `I i = new X(); i.hashCode()` still links:
interface method resolution finds `Object`'s public `hashCode` (§5.4.3.4 step 2), and selection runs
it on `X`, both before and after. -/
def ifaceHashCodeRemoved : Case where
  name := "ifaceHashCodeRemoved"
  mima := none
  v0 := [object, (.I, { header := ifaceO, methods := [(.hashCode, .i, abs)] })]
  v1 := [object, (.I, { header := ifaceO })]
  client := [(.X, { header := { super := some .O, ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .hashCode .i .X] }

/-- An interface drops its declaration of `finalize()V`, which the client's `X` implements. Step 2
of §5.4.3.4 finds only public methods of `Object`, and `Object.finalize` is protected, so
`i.finalize()` no longer resolves. -/
def ifaceFinalizeRemoved : Case where
  name := "ifaceFinalizeRemoved"
  mima := some "InaccessibleMethodProblem"
  v0 := [object, (.I, { header := ifaceO, methods := [(.finalize, .v, abs)] })]
  v1 := [object, (.I, { header := ifaceO })]
  client := [(.X, { header := { super := some .O, ifaces := [.I] }, methods := [(.finalize, .v, inst)] })]
  prog := { sites := [invokeinterface .I .finalize .v .X] }

def jObject : List Case := [ifaceHashCodeRemoved, ifaceFinalizeRemoved]
/-! ## Track J4: method bodies

A method's body is the sites it runs; a `this` site's receiver is the class the caller instantiated. -/

/-- `A.m()V` calls `this.m()I`; the client's `X extends A` overrides `m()I`, and a call of `A.m()V`
on an `X` enters `A.m()V` and then `X.m()I`. -/
def thisCallOverridden : Case where
  name := "thisCallOverridden"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, { body := [invokevirtualThis .A .m .i] }), (.m, .i, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { body := [invokevirtualThis .A .m .i] }), (.m, .i, inst)] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .i, inst)] })]
  prog := { sites := [invokevirtual .A .m .v .X] }

/-- A method that calls itself on `this` runs out of fuel: the model's bound, not a JVM error. -/
def selfCall : Case where
  name := "selfCall"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, { body := [invokevirtualThis .A .m .v] })] })]
  v1 := [(.A, { methods := [(.m, .v, { body := [invokevirtualThis .A .m .v] })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

/-- A template method: `A.run()` calls `this.m()`, and `m` becomes abstract. The client's
`X extends A` never calls `m`; it fails inside the library's `run` (`AbstractMethodError`). -/
def hookBecomesAbstract : Case where
  name := "hookBecomesAbstract"
  mima := some "DirectAbstractMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.run, .v, { body := [invokevirtualThis .A .m .v] }), (.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.run, .v, { body := [invokevirtualThis .A .m .v] }), (.m, .v, abs)] })]
  client := [(.X, { header := { super := some .A } })]
  prog := { sites := [invokevirtual .A .run .v .X] }

/-- The hook becomes private: the library's `this.m()` now runs `A.m` itself, not the client's
override (a private method is not overridden). Links, and runs different code. -/
def hookBecomesPrivate : Case where
  name := "hookBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.run, .v, { body := [invokevirtualThis .A .m .v] }), (.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.run, .v, { body := [invokevirtualThis .A .m .v] }), (.m, .v, { access := .priv })] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  prog := { sites := [invokevirtual .A .run .v .X] }

/-- An interface gains an abstract hook that its default `run()` calls (MiMa's
`ReversedMissingMethodProblem`). The client's `X implements J` already had a package-private `m()I`:
it overrides `J.m` (§5.4.5), so selection finds it, and `invokeinterface` then fails because it is not
public (JVMS §6.5 `invokeinterface`, run-time exceptions). Found by the 17 reversed edits of
`MiMa.Reversed`; the same rule as Track J7's `pkgMethodAboveDefault`. -/
def ifaceHookPackagePrivate : Case where
  name := "ifaceHookPackagePrivate"
  mima := some "ReversedMissingMethodProblem"
  v0 := [(.J, { header := { iface with pkg := 1 }, methods := [(.run, .v, inst)] })]
  v1 := [(.J, { header := { iface with pkg := 1 },
                methods := [(.run, .v, { body := [invokeinterfaceThis .J .m .i] }), (.m, .i, abs)] })]
  client := [(.X, { header := { ifaces := [.J] }, methods := [(.m, .i, { access := .pkg })] })]
  prog := { sites := [invokeinterface .J .run .v .X] }

/-- `A` and its inner class `B` as javac compiles them: `A` is the nest host and lists `B`, `B` names
`A`; `B.run()` calls `A`'s private `m` (`new A().m()`). -/
def nestA (members : List C) : Classfile C N D :=
  { header := { p1 with nestMembers := members }, methods := [(.m, .v, { access := .priv })] }
def nestB (host : Option C) : Classfile C N D :=
  { header := { p1 with nestHost := host }, methods := [(.run, .v, { body := [invokevirtual .A .m .v .A] })] }

/-- The inner class leaves the nest (`A`'s `NestMembers` no longer lists `B`, as when `B` is
recompiled as a top-level class beside an old `B`): the library's own call of `A.m` from `B.run` fails
(JVMS §5.4.4). The client only calls `B.run`. -/
def nestMemberRemoved : Case where
  name := "nestMemberRemoved"
  mima := none
  v0 := [(.A, nestA [.B]), (.B, nestB (some .A))]
  v1 := [(.A, nestA []), (.B, nestB (some .A))]
  prog := { sites := [invokevirtual .B .run .v .B] }

/-- The inner class moves to another nest: `B`'s `NestHost` is now `I`, which lists it, so `A` and
`B` are no longer nestmates. -/
def nestHostChanged : Case where
  name := "nestHostChanged"
  mima := none
  v0 := [(.A, nestA [.B]), (.B, nestB (some .A)), (.I, { header := p1 })]
  v1 := [(.A, nestA [.B]), (.B, nestB (some .I)), (.I, { header := { p1 with nestMembers := [.B] } })]
  prog := { sites := [invokevirtual .B .run .v .B] }

/-- The Track J4 cases the probe runs (`selfCall` overflows the JVM's stack instead). -/
def j4 : List Case :=
  [thisCallOverridden, hookBecomesAbstract, hookBecomesPrivate, ifaceHookPackagePrivate, nestMemberRemoved,
   nestHostChanged]

/-! ## JVMS §5.3.5's order of loading checks

§5.3.5 resolves the superclass by §5.4.3.1, whose last step is access control, and then checks it (step
3: not an interface, not final, sealed), and only then resolves and checks the superinterfaces (step
4). Each case breaks two of these at once, so the exception says which check ran first. HotSpot 21, 25
and 27 check in another order, and the model follows HotSpot (`Jvm.loadK`). -/

/-- The superclass is final and, from the client's package, inaccessible. By §5.3.5 step 3 the
superclass's resolution fails its access check first, an `IllegalAccessError`; HotSpot reports the
final superclass ("cannot inherit from final class"), an `IncompatibleClassChangeError`. -/
def finalSuperInaccessible : Case where
  name := "finalSuperInaccessible"
  mima := none
  v0 := [(.A, { header := { p1 with isFinal := true, isPublic := false } })]
  v1 := [(.A, { header := { p1 with isFinal := true, isPublic := false } })]
  client := [(.X, { header := { super := some .A } })]
  prog := { loads := [.X] }

/-- A superinterface that is a class, and an inaccessible superclass. §5.3.5 resolves the superclass in
step 3, before the superinterfaces in step 4, so an `IllegalAccessError`; HotSpot checks the
superinterfaces first ("can not implement B, because it is not an interface"), an
`IncompatibleClassChangeError`. -/
def ifaceNotIfaceSuperInaccessible : Case where
  name := "ifaceNotIfaceSuperInaccessible"
  mima := none
  v0 := [(.A, { header := { p1 with isPublic := false } }), (.B, {})]
  v1 := [(.A, { header := { p1 with isPublic := false } }), (.B, {})]
  client := [(.X, { header := { super := some .A, ifaces := [.B] } })]
  prog := { loads := [.X] }

def jSpec : List Case := [finalSuperInaccessible, ifaceNotIfaceSuperInaccessible]

def all : List Case :=
  [methodRemoved, resultTypeChanged, classBecomesInterface, becomesStatic, becomesAbstract,
   becomesFinal, methodBecomesFinal, superclassRemoved, defaultRemoved, defaultConflict,
   overrideAdded, pulledUp]

example : classBecomesInterface.before = .ok [.A] := by decide
example : methodRemoved.before = .ok [.A] ∧ methodRemoved.after = .error .noSuchMethod := by
  decide
example : resultTypeChanged.after = .error .noSuchMethod := by decide
example : classBecomesInterface.after = .error .incompatibleClassChange := by decide
example : becomesStatic.after = .error .incompatibleClassChange := by decide
example : becomesAbstract.after = .error .instantiation := by decide
example : becomesFinal.before = .ok [] ∧ becomesFinal.after = .error .finalSuper := by
  decide
example : methodBecomesFinal.after = .error .finalOverride := by decide
example : superclassRemoved.after = .error .noSuchMethod := by decide
example : defaultRemoved.before = .ok [.I] ∧ defaultRemoved.after = .error .abstractMethod := by
  decide
example : defaultConflict.before = .ok [.I] ∧
    defaultConflict.after = .error .incompatibleClassChange := by decide
example : overrideAdded.before = .ok [.A] ∧ overrideAdded.after = .ok [.B] := by decide
example : pulledUp.before = .ok [.B] ∧ pulledUp.after = .ok [.A] := by decide

/-- The two compatible edits change the footprint: `link_congr` does not apply, and a Zinc-style
"same answers on the trace" test would flag them. -/
example : (footprint overrideAdded.w0 overrideAdded.prog).any
    (fun q => !agrees overrideAdded.w0 overrideAdded.w1 q) = true := by
  decide

example : methodBecomesPrivate.before = .ok [.A] ∧ methodBecomesPrivate.after = .error .illegalAccess := by decide
example : methodBecomesPackagePrivate.before = .ok [.A] ∧ methodBecomesPackagePrivate.after = .error .illegalAccess := by decide
example : classBecomesPackagePrivate.before = .ok [.A] ∧ classBecomesPackagePrivate.after = .error .illegalAccess := by decide
example : methodBecomesProtected.before = .ok [.A] ∧ methodBecomesProtected.after = .error .illegalAccess := by decide
example : methodBecomesProtectedSub.before = .ok [.A] ∧ methodBecomesProtectedSub.after = .ok [.A] := by decide
example : methodBecomesProtectedOther.before = .ok [.A] ∧ methodBecomesProtectedOther.after = .error .verify := by decide
example : overrideCutByPackage.before = .ok [.X] ∧ overrideCutByPackage.after = .ok [.A] := by decide
example : overrideBecomesPrivate.before = .ok [.B] ∧ overrideBecomesPrivate.after = .ok [.A] := by decide
example : superCallPulledUp.before = .ok [.B] ∧ superCallPulledUp.after = .ok [.A] := by decide
example : superCallRemoved.before = .ok [.B] ∧ superCallRemoved.after = .error .noSuchMethod := by decide
example : superCallAbstract.before = .ok [.B] ∧ superCallAbstract.after = .error .abstractMethod := by decide
example : defaultSuperCallAbstract.before = .ok [.I] ∧ defaultSuperCallAbstract.after = .error .abstractMethod := by decide
example : staticIfaceMethodRemoved.before = .ok [.I] ∧ staticIfaceMethodRemoved.after = .error .noSuchMethod := by decide
example : staticMovedToIface.before = .ok [.A] ∧ staticMovedToIface.after = .error .noSuchMethod := by decide
example : defaultBecomesStatic.before = .ok [.I] ∧ defaultBecomesStatic.after = .error .incompatibleClassChange := by decide
example : defaultBecomesPrivate.before = .ok [.I] ∧ defaultBecomesPrivate.after = .error .illegalAccess := by decide
example : fieldRemoved.before = .ok [.A] ∧ fieldRemoved.after = .error .noSuchField := by decide
example : fieldBecomesStatic.before = .ok [.A] ∧ fieldBecomesStatic.after = .error .incompatibleClassChange := by decide
example : fieldBecomesFinal.before = .ok [.A] ∧ fieldBecomesFinal.after = .error .illegalAccess := by decide
example : fieldBecomesPrivate.before = .ok [.A] ∧ fieldBecomesPrivate.after = .error .illegalAccess := by decide
example : fieldShadowed.before = .ok [.A] ∧ fieldShadowed.after = .ok [.B] := by decide
example : fieldIfaceBeforeSuper.before = .ok [.A] ∧ fieldIfaceBeforeSuper.after = .ok [.I] := by decide
example : putstaticBecomesFinal.before = .ok [.A] ∧ putstaticBecomesFinal.after = .error .illegalAccess := by decide
example : transitiveOverride.before = .ok [.I] ∧ transitiveOverride.after = .ok [.X] := by decide
example : methodBecomesFinalBehind.before = .ok [] ∧ methodBecomesFinalBehind.after = .error .finalOverride := by decide

example : classBecomesSealed.before = .ok [] ∧ classBecomesSealed.after = .error .incompatibleClassChange := by decide
example : classBecomesSealedPermitting.after = .ok [] := by decide
example : ifaceBecomesSealed.before = .ok [] ∧ ifaceBecomesSealed.after = .error .incompatibleClassChange := by decide
example : sealedPermitsNonPublicElsewhere.after = .error .incompatibleClassChange := by decide
example : sealedPermitsPublicElsewhere.after = .ok [] := by decide
example : ctorRemoved.before = .ok [.A] ∧ ctorRemoved.after = .error .noSuchMethod := by decide
example : ctorBecomesPrivate.before = .ok [.A] ∧ ctorBecomesPrivate.after = .error .illegalAccess := by decide
example : ctorBecomesPackagePrivate.before = .ok [.A] ∧ ctorBecomesPackagePrivate.after = .error .illegalAccess := by decide
example : ctorPulledUp.before = .ok [.B] ∧ ctorPulledUp.after = .error .noSuchMethod := by decide
example : ctorClassBecomesAbstract.before = .ok [.A] ∧ ctorClassBecomesAbstract.after = .error .instantiation := by decide

example : pkgMethodAboveDefault.before = .ok [.I] ∧ pkgMethodAboveDefault.after = .error .illegalAccess := by decide
example : fieldIfaceDepthBeforeSuper.before = .ok [.A] ∧ fieldIfaceDepthBeforeSuper.after = .ok [.K] := by decide
example : ifaceHashCodeRemoved.before = .ok [.O] ∧ ifaceHashCodeRemoved.after = .ok [.O] := by decide
example : ifaceFinalizeRemoved.before = .ok [.X] ∧ ifaceFinalizeRemoved.after = .error .noSuchMethod := by decide
example : thisCallOverridden.before = .ok [.A, .X] := by decide
example : selfCall.before = .error .outOfFuel := by decide
example : hookBecomesAbstract.before = .ok [.A, .A] ∧
    hookBecomesAbstract.after = .error .abstractMethod := by decide
example : hookBecomesPrivate.before = .ok [.A, .X] ∧ hookBecomesPrivate.after = .ok [.A, .A] := by decide
example : ifaceHookPackagePrivate.before = .ok [.J] ∧
    ifaceHookPackagePrivate.after = .error .illegalAccess := by decide
example : nestMemberRemoved.before = .ok [.B, .A] ∧ nestMemberRemoved.after = .error .illegalAccess := by decide
example : nestHostChanged.before = .ok [.B, .A] ∧ nestHostChanged.after = .error .illegalAccess := by decide

/-- The model follows HotSpot, not the order of §5.3.5. -/
example : finalSuperInaccessible.before = .error .finalSuper ∧
    ifaceNotIfaceSuperInaccessible.before = .error .incompatibleClassChange := by decide

end Jvm.Catalogue
