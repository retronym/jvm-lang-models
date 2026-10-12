# Upstream drafts

Drafts of reports to the Scala projects arising from the models. None has been posted; each says where it would go. Once one is posted, replace its draft with a link.

| Draft | Venue | Finding |
|---|---|---|
| [dotc-reabstraction-direct-parent.md](dotc-reabstraction-direct-parent.md) | scala/scala3 issue | Trait re-abstraction in Scala 3 depends on whether the concrete trait is a direct parent |
| [spec-reabstraction.md](spec-reabstraction.md) | scala/scala3 issue (spec) | SLS §5.1.4 says a concrete definition always overrides an abstract one; neither compiler does that |
| [reabstraction-discussion.md](reabstraction-discussion.md) | contributors.scala-lang.org | What should re-abstraction mean? Four answers: spec, scalac, dotc, javac/JVM |
| [jvms-derivation-check-order.md](jvms-derivation-check-order.md) | OpenJDK JBS (hotspot/runtime, or the JVMS) | HotSpot checks superinterfaces and a final superclass before the superclass's access, against the step order of JVMS §5.3.5 |
| [mixin-final-override-recheck.md](mixin-final-override-recheck.md) | note, not a report | 2.13's re-check of overriding pairs across non-suffix linearizations is intentional ([scala/bug#11136](https://github.com/scala/bug/issues/11136)) |

The cases were found by embedding the toy language of [Flat.lean](../../packages/zinc/Zinc/Bridges/Flat.lean) into the shared Scala semantics ([FlatShared.lean](../../packages/zinc/Zinc/Bridges/FlatShared.lean)) and checking the disagreements against scalac 2.12.21, 2.13.18 and dotc 3.9.0. The model's account is in [track-s.md](../../packages/scala/docs/track-s.md).
