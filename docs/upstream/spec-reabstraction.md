# Draft: scala/scala3 issue (specification)

**Title:** SLS §5.1.4 says a concrete definition always overrides an abstract one, but neither compiler does that

§5.1.4 (Overriding) says:

> a concrete definition always overrides an abstract definition

Read literally, a member that is concrete anywhere in the linearization is never deferred again by a later abstract declaration. Both compilers re-abstract in some cases.

A class re-declaring a member as abstract is rejected by both scalac 2.13.18 and dotc 3.9.0:

```scala
trait M { def m: Int = 1 }
class A extends M
abstract class B extends A { def m: Int }
class C extends B with M    // 2.13: "class C needs to be abstract"; 3.9: "... deferred declaration of method m in class B ... not implemented"
```

A trait re-declaring it is accepted by scalac 2.13 and rejected by dotc, unless the concrete trait is also a direct parent (see the companion issue):

```scala
trait M { def m: String = "" }
trait A extends M { def m: String }
class B extends A           // 2.13: ok; 3.9: "class B needs to be abstract"
```

Java and the JVM take the other extreme: an abstract redeclaration always hides an inherited concrete one (JLS §9.4.1, JVMS §5.4.6).

Suggested resolution: state the rule the compilers implement. A class's abstract declaration defers the member for its subclasses, and a trait's does too, except where a concrete member is supplied by a direct parent (dotc). Alternatively, decide the intended rule first (see the discussion draft). In either case, the sentence above should be qualified.
