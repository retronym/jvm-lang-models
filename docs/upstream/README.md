# Upstream drafts

Drafts of reports to the Scala projects arising from the models. None has been posted; each says where it would go. Once one is posted, replace its draft with a link.

| Draft | Venue | Finding |
|---|---|---|
| [dotc-reabstraction-direct-parent.md](dotc-reabstraction-direct-parent.md) | scala/scala3 issue | Trait re-abstraction in Scala 3 depends on whether the concrete trait is a direct parent |
| [spec-reabstraction.md](spec-reabstraction.md) | scala/scala3 issue (spec) | SLS §5.1.4 says a concrete definition always overrides an abstract one; neither compiler does that |
| [reabstraction-discussion.md](reabstraction-discussion.md) | contributors.scala-lang.org | What should re-abstraction mean? Four answers: spec, scalac, dotc, javac/JVM |
| [dotc-member-bounds-unchecked.md](dotc-member-bounds-unchecked.md) | scala/scala3 issue | dotc does not check a type member's declared bounds, so `trait B { type L >: Int <: String }` and a `null` path give a cast-free ClassCastException (Track T) |
| [mima-pkg-private-above-default.md](mima-pkg-private-above-default.md) | scala-garden/mima issue | A package-private method added to a class breaks `invokeinterface` on a subclass that inherits a default (JVMS §6.5); MiMa 1.2.1 silent (Track J7, `pkgMethodAboveDefault`) |
| already filed: [scala/bug#12164](https://github.com/scala/bug/issues/12164) (open) | scala/bug | Scala 2 reads a type member of `A with B` from the last parent, not from both bindings (SLS §3.2.7, §3.4 make every parent's declaration a member binding), so `def up(o: A with B)(x: Int): o.L = x` with `A { type L >: Int }`, `B { type L <: Any }` is rejected, `B with A` accepted, and Scala 3 accepts both (Track T). A possible comment on the issue: that two-trait reproducer, checked on 2.12.21 and 2.13.18 |
| [Linking page](../../literate/Literate/Linking.lean) | note, not a report | JVMS §6.5's `invokeinterface` access check after selection, which the model lacked until Track J7: a model finding, quoted verbatim on the literate Linking page |
| [mixin-final-override-recheck.md](mixin-final-override-recheck.md) | note, not a report | 2.13's re-check of overriding pairs across non-suffix linearizations is intentional ([scala/bug#11136](https://github.com/scala/bug/issues/11136)) |

The cases were found by embedding the toy language of [Flat.lean](../../packages/zinc/Zinc/Bridges/Flat.lean) into the shared Scala semantics ([FlatShared.lean](../../packages/zinc/Zinc/Bridges/FlatShared.lean)) and checking the disagreements against scalac 2.12.21, 2.13.18 and dotc 3.9.0. The model's account is in [track-s.md](../../packages/scala/docs/track-s.md).
