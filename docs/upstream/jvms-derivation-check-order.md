# HotSpot checks a class's superinterfaces and its superclass's finality before the superclass's access

Draft, not posted. Venue: OpenJDK JBS, component hotspot/runtime (or specification/vm if the JVMS is meant to leave the order open).

**JVMS 25 §5.3.5.** Deriving a class `C` resolves its direct superclass by §5.4.3.1 (step 3), whose last step is access control (§5.4.4); only then does it check that the superclass is not an interface, not final and permits `C`; and only then (step 4) does it resolve and check the direct superinterfaces. So when a class breaks two of these, the specification says which exception is thrown.

**HotSpot 21, 25 and 27** check in another order: the superinterfaces first, and the superclass's finality before its accessibility. Two classfiles, rendered with the Classfile API by [`packages/jvm/probes`](../../packages/jvm/probes):

- `X extends p1.A`, where `p1.A` is final and package-private, `X` in another package: §5.3.5 gives `IllegalAccessError` (the superclass's resolution fails its access check); HotSpot throws `IncompatibleClassChangeError: class X cannot inherit from final class p1.A` ([`Catalogue.finalSuperInaccessible`](../../packages/jvm/Jvm/Catalogue.lean#L677)).
- `X extends p1.A implements B`, where `p1.A` is package-private and `B` is a class: §5.3.5 gives `IllegalAccessError`; HotSpot throws `IncompatibleClassChangeError: class X can not implement B, because it is not an interface` ([`Catalogue.ifaceNotIfaceSuperInaccessible`](../../packages/jvm/Jvm/Catalogue.lean#L689)).

javac never emits either; only a class whose superclass changed after it was compiled meets them. The question for the report: is the step order of §5.3.5 normative? If it is, HotSpot does not conform; if not, the JVMS could say that the order of these checks is unspecified, as it does for when resolution happens (§5.4).

The model follows HotSpot ([`Jvm.loadK`](../../packages/jvm/Jvm/Link.lean#L339)), and the [specification ledger](../specification-ledger.md) records the disagreement.
