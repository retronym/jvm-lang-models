# dotc: DropOuterAccessors keeps the outer accessors of named nested classes, because its group runs after Flatten

Venue: scala/scala3 issue (area:transform, itype:performance or bug). Draft, not posted.

## Compiler version

3.9.0 (and `main` at [`d168df2a76`](https://github.com/scala/scala3/tree/d168df2a76)).

## Minimized code

```scala
class Q {
  def n = 2
  def o = { class M { def z = n }; new M().z }
  private class I { def z = n }
  def p = new I().z
}
```

## Output

`javap -p Q\$M\$1 Q\$I`: both classes keep their outer accessor, though nothing calls it (`z` reads the `$outer` field directly):

```
public class Q$M$1 {
  private final Q $outer;
  public Q$M$1(Q);
  public int z();
  public final Q Q$_$M$$$outer();
}
public class Q$I {
  private final Q $outer;
  ...
  public final Q Q$I$$$outer();
}
```

## Expectation

[`a475e47`](https://github.com/scala/scala3/commit/a475e47fbec8b236a2c1c876cb022d87f6a9b9b4) and [`363985e`](https://github.com/scala/scala3/commit/363985e1c5a13aa7fcc49d033127bc28e6520c6e) ("Drop more outer accessors": "classes that are visible only in one toplevel class") should drop both accessors. They do for anonymous classes, which is what [`tests/run/i8033.scala`](https://github.com/scala/scala3/blob/d168df2a76/tests/run/i8033.scala) covers.

## Cause

`CountOuterAccesses` and `DropOuterAccessors` both ask [`CountOuterAccesses.mightBeDropped`](https://github.com/scala/scala3/blob/d168df2a76/compiler/src/dotty/tools/dotc/transform/CountOuterAccesses.scala), whose `isLocal(sym.owner)` depends on the class's owner and `topLevelClass`. A fused group runs all its miniphases at the phase after its last one ([`MegaPhase.run`: `atPhase(miniPhases.last.next)`](https://github.com/scala/scala3/blob/d168df2a76/compiler/src/dotty/tools/dotc/transform/MegaPhase.scala#L491-L493), since [scala/scala3#3350](https://github.com/scala/scala3/pull/3350)). `DropOuterAccessors` is in a group with `Flatten`, so it sees the owners after Flatten has moved every nested class to its package, and `isLocal` is false for any named nested class. `CountOuterAccesses`, in the group before, sees them before Flatten and counts. The two phases disagree, and the drop never happens.

Measured on the outer accessors of `tests/run/llift.scala` by evaluating `mightBeDropped` at each phase after the run:

```
Test$_$T1$_$T2$$$outer in T2$1: Count true, Drop unfused true, Drop fused false
Test$_$T1$_$C2$$$outer in C2$1: Count true, Drop unfused true, Drop fused false
Test$_$C1$$$outer in C1$1:      Count true, Drop unfused true, Drop fused false
```

Compiling with every miniphase in a group of its own (so `DropOuterAccessors` runs at its own phase) drops the accessors above, and exposes a second problem: the assertion `stat.rhs.isInstanceOf[RefTree]` in `dropOuterAccessor` fails on `tests/run/llift.scala`, for the deferred outer accessor of a trait nested in a local trait:

```
java.lang.AssertionError: assertion failed: DefDef(Test$_$T1$_$T2$$$outer,List(List()),TypeTree[TypeRef(NoPrefix,trait T1$4)],EmptyTree)
	at dotty.tools.dotc.transform.DropOuterAccessors.dropOuterAccessor$1(DropOuterAccessors.scala:47)
```

So a fix that evaluates `mightBeDropped` before Flatten (for instance `atPhase(thisPhase)(mightBeDropped(sym))` in `DropOuterAccessors`, or `atPhase(ctx.base.countOuterAccessesPhase.next)`) also needs to skip deferred accessors.

## How it was found

By compiling `tests/run/*.scala` twice, with dotc's phase groups and with every miniphase in a group of its own, and comparing the output byte for byte ([`Fusion3.scala`](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/probes/phases/Fusion3.scala), [`OuterAccessors3.scala`](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/probes/phases/OuterAccessors3.scala)). In 13 of the 83 files whose output differs, unfused drops an outer accessor (or field) that fused keeps.
