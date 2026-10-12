# asSeenFrom, formalized

A small Lean 4 model (no Mathlib) of how scalac and the IntelliJ Scala plugin compute the type of a selected member, and a proof of the conditions under which they agree. Its consumer is `SubstitutorInvariants` in [retronym/intellij-scala#5](https://github.com/retronym/intellij-scala/issues/5), which turns each theorem below into a runtime check.

## Why

A member's declared type is written from inside its class: `def typer: Typer` in `trait Typers` means `Typers.this.Typer`. When code selects the member through a path, as `global.analyzer.typer`, the `Typers.this` in that type must be rewritten onto the path, giving `global.analyzer.Typer`. scalac does this with one map, `info(m).asSeenFrom(pre, owner(m))`. The plugin does it with an `ScSubstitutor` built up during resolution and applied when the reference's type is computed.

The plugin's false errors on cake-pattern code (scala/scala's own compiler, for one) came from substitutors that were built wrong. The rewrite itself is simple; what goes wrong is which rewrites a substitutor holds, where each one starts, and which types it is later applied to. A wrongly built substitutor does no harm where it is built. It surfaces later, far away, as a conformance or override error on some unrelated expression, and each such symptom had to be traced back by hand. **This model defines "well formed" precisely, so that a wrong substitutor can be caught at the line that mints it rather than diagnosed from its symptoms.**

## Terms

An `ScSubstitutor` is a sequence of simple updates applied one after the other; `a.followed(b)` appends `b`'s updates after `a`'s, so it applies `a` first. Below, a **chain** is shorthand for an `ScSubstitutor` and a **link** for one of its updates. Two kinds of link matter: a type-argument binding (`A -> Any`), and a this-type rewrite (`ThisTypeSubstitution`), which replaces `D.this` leaves by a prefix.

A this-type rewrite has an **anchor**: the class its input type was written in, scalac's `clazz` in `tp.asSeenFrom(pre, clazz)`, which for a member's type is `sym.owner`. scalac's walk starts at the anchor and climbs outwards through the enclosing classes, stepping along the prefix's base-type prefixes in parallel, and rewrites `D.this` when the climb reaches `D`. **The anchor decides which this-types a link can reach, and onto which piece of the prefix each one goes.**

In the plugin's notation, where `>>` separates links applied left to right:

- **Well formed.** Resolving `global.analyzer.typer`, declared as `Typers.this.Typer`, gives `` ScSubstitutor(`this` -> global.analyzer.type asSeenFrom Typers) ``. The link is anchored at `Typers`, the class the type was written in, so applied to `Typers.this.Typer` it gives `global.analyzer.Typer`, as scalac does.
- **Malformed: a link stored where it does not belong.** Inside `class IO`, the body of `case FlatMap(f, k) =>` used to resolve every reference with `` ScSubstitutor(`this` -> IO.this.type asSeenFrom FlatMap >> Map(A -> Any, B -> A)) ``. The type bindings are the pattern's to give, but the this-type rewrite was left over from typing `FlatMap.unapply`, and it was applied to the type of every reference in the body.
- **Malformed: no anchor.** `x == y` resolved `==` with `` ScSubstitutor(`this` -> x.type) ``. With no anchor there is no climb, so the plugin guessed by inheritance alone which this-types to replace.

## What is proved

The model abstracts the environment to two facts read off base types (`Model.lean`) and makes one assumption, **lockstep**: an `asSeenFrom` map commutes with taking a base type's prefix. scalac relies on this implicitly; for the plugin it is the contract `BaseTypes.baseType` must meet, which the TCK's baseType dimension checks empirically. Given lockstep, the theorems below are what the plugin's checks rest on. Each check states a theorem's hypothesis, so a violation means the chain is outside the model, not that its result is necessarily wrong.

| Theorem | Guarantees | Plugin check |
|---|---|---|
| [`Chain.compose`](IntelliJ/Chain.lean#L82) | two links in sequence are one link, from the first prefix as seen by the second, provided the first link rewrites every this-type of its input (`inView`) | A5: a this-type on the anchor's owner chain that a link leaves alone is one that scalac's walk also leaves alone |
| [`Chain.chain_is_single`](IntelliJ/Chain.lean#L116) | by induction, a whole chain is one `asSeenFrom`, so one pass suffices and no output needs rewriting again | I4: the census that justified deleting the no-self-embedding brake |
| [`Chain.chain_is_intended`](IntelliJ/Chain.lean#L194) | if each link is anchored at the class of the prefix composed so far (`wellAnchored`), that one `asSeenFrom` is from the *intended* prefix | A3, A4: measurements, not gates (see link order below) |
| [`Chain.idempotent`](IntelliJ/Chain.lean#L138), [`Chain.idempotent_of_fixed`](IntelliJ/Chain.lean#L231) | a link that maps its own target to itself (`hp`) can be re-applied to its own output without effect; `fixedTarget` is a syntactic condition sufficient for `hp` | A1: checks `hp` directly, by applying the link to its target |
| [`Chain.once_is_scalac`](IntelliJ/Chain.lean#L418), [`Chain.selfRooted_twice_diverges`](IntelliJ/Chain.lean#L393) | a link whose target is a path rooted in the class it rewrites ([`SelfRooted`](IntelliJ/Chain.lean#L349)) never satisfies `hp`, yet the chain is scalac's result if no later link moves that target; a second copy of the link always moves it ([`selfRooted_dup_not_fixed`](IntelliJ/Chain.lean#L427)), and `l >> l` diverges from scalac | A1: a link that fails `hp` must be self-rooted, and a self-rooted link may occur at most once in a chain |
| [`Relax.partRooted_moves_target`](IntelliJ/Relaxations.lean#L222), [`Relax.partRooted_twice_diverges`](IntelliJ/Relaxations.lean#L241), [`Relax.partRooted_once_is_scalac`](IntelliJ/Relaxations.lean#L258) | a link whose compound target has a part rooted in the anchor's this-type (`T1.this -> T1 with T1.this.M3`) always moves its target, is scalac's result once, and diverges twice (the `processType` duplicate) | A1 relaxation (a): admit once per chain |
| [`Relax.outerRooted_fixed_iff_owner`](IntelliJ/Relaxations.lean#L348), [`Relax.outerRooted_once_is_scalac`](IntelliJ/Relaxations.lean#L384) | a path target rooted in the anchor's owner (`I2.this -> T2.this.v12.type`) moves exactly when `(v12 baseType I2).prefix` is not `T2.this`; once it is the model's scalac, which substitutes unstable prefixes where real scalac captures them existentially | A1 relaxation (b): admit once per chain, against model-scalac only |
| [`Relax.idempotent_eqv`](IntelliJ/Relaxations.lean#L484), [`Relax.once_is_scalac_eqv`](IntelliJ/Relaxations.lean#L510) | up to `Eqv` (singleton aliases, compound commutativity, associativity, idempotence), under the congruence assumptions [`PathEqv`](IntelliJ/Relaxations.lean#L438), a link that gives its target back is idempotent and a chain is scalac's | A1 relaxation (c): justifies `=:=` modulo aliases and reordering, narrower than the mutual conformance the plugin uses |
| [`Relax.once_is_scalac_of_disjoint`](IntelliJ/Relaxations.lean#L539) | no this-type of the first target is a later link's anchor or encloses it, so no later link moves the target | closes the gap between A1's "at most one copy" and [`once_is_scalac`](IntelliJ/Chain.lean#L418)'s hypothesis |
| [`Relax.pluginAsf_agrees`](IntelliJ/Relaxations.lean#L294) | one pass of the plugin's map is scalac's where the fallback does not fire on the input, whatever it does on the target | A1 relaxation (a), inheritor case: the one pass only |
| [`Chain.stateSafe_preserves_this`](IntelliJ/Chain.lean#L285) | a chain with no this-type rewrites keeps every this-type of its input, so storing it in resolver state cannot re-anchor other references' types | A2: fails the tests if violated |
| [`IntelliJ.agrees`](IntelliJ/Plugin.lean#L72) | the plugin's walk, fallback included, equals scalac's wherever the fallback does not fire; both start from an anchor | A6: every this-type rewrite has an anchor, now true by construction |

The plugin's scaladocs also use the earlier labels C1, C2, C3 for `wellAnchored`, `fixedTarget`, `stateSafe`.

**Link order.** The model's well-anchored chain has the shape `sig_C >> use`: the signature substitutor of `C` first puts a member declared in a superclass into `C`'s view, then the use-site link, anchored at `C`, views it from the prefix. The plugin builds that order only on some routes (a this-link that arrives through resolve state, after `TypeDefinitionMembers` has put `sig_C` first), and even there anchors the use-site link at `owner(m)`, not at `C`. On the main route, `ScalaResolveState.substitutorWithThisType(owner(m))` *prepends* the use-site link, giving `use >> sig_C`: the use-site link runs first, on the declared type, anchored at the class it was written in, and `sig_C` sees only what it left. Its first link is already scalac's whole map, `asSeenFrom(pre, owner(m))`, but the chain is not the shape `wellAnchored` describes, and A3 and A4 fire on it by the hundreds of thousands. **A3 and A4 measure how far the plugin's chains are from the model's shape; they are not a gate.**

**Self-rooted links.** [`idempotent_of_fixed`](IntelliJ/Chain.lean#L231) is a sufficient condition for re-applying a link, and over scala/scala the plugin mints links that do not meet it and are still right. In `Scanners.scala`, `class UnitScanner { lazy val parensAnalyzer = new ParensAnalyzer(…) }` and `class ParensAnalyzer extends UnitScanner`; inside `UnitScanner`, `parensAnalyzer.balance(token)` views an inherited member through `` `this` -> UnitScanner.this.parensAnalyzer.type asSeenFrom UnitScanner ``. The `UnitScanner.this` in the member's type is the receiver; the one inside the target is the enclosing scanner, a different instance with the same name. Like scalac's walk, the plugin's engine replaces the first and hands the result to the *next* link, never back to the same one, so the second survives and the result is scalac's. A second copy of the link later in the chain cannot tell the two apart and gives `UnitScanner.this.parensAnalyzer.parensAnalyzer.T`. [`once_is_scalac`](IntelliJ/Chain.lean#L418) proves the first half for any chain whose later links leave the target alone, as a corollary of `chain_is_single`: the chain is one walk from the composed prefix, and those links leave that prefix where it was. [`selfRooted_twice_diverges`](IntelliJ/Chain.lean#L393) proves the second half, and `Cases.C` decides the example. **A self-rooted link is correct exactly once, so the check that fits it is "at most once per chain", not "idempotent".**

What is not proved: that `BaseTypes.baseType` satisfies lockstep (an assumption here, checked by the TCK), and termination of the plugin's engine as a whole, which feeds link outputs back into resolution. `chain_is_single` says that for chains in the model no output needs re-rewriting, which is what made the brake redundant.

## Files

| File | Content |
|---|---|
| `Model.lean` | classes as owner paths, types with this-leaves, a `World` of base-type facts |
| [`Scalac.lean`](IntelliJ/Scalac.lean) | scalac's `thisTypeAsSeen` and `asSeenFrom` as structural recursion, so termination is the checker's; `inView` |
| [`Port.lean`](IntelliJ/Port.lean) | `Ty` as an instance of `ScalaTypes.AsSeenFrom` (the same walk for any type language with this-type and class-parameter leaves, with the composition law proved once; shared with the Scala layer's lowering) (this-leaves only); [`asf_eq`](IntelliJ/Port.lean#L85): [`Scalac.asf`](IntelliJ/Scalac.lean#L34) is the shared map; lockstep carries over. [`Chain.compose`](IntelliJ/Chain.lean#L82) is proved from the shared theorem through it |
| [`Chain.lean`](IntelliJ/Chain.lean) | lockstep; `compose`, `chain_is_single`, `idempotent`; then the checkable conditions `wellAnchored`, `fixedTarget`, `stateSafe` and their theorems; last, self-rooted links and [`once_is_scalac`](IntelliJ/Chain.lean#L418) |
| [`Relaxations.lean`](IntelliJ/Relaxations.lean) | three shapes of link that fail A1's arms and are admitted by a relaxation: compound self-rooted, outer-rooted, respelled; and a checkable condition for [`once_is_scalac`](IntelliJ/Chain.lean#L418) |
| [`Plugin.lean`](IntelliJ/Plugin.lean) | the plugin's walk with its narrow-against-target fallback; `agrees` |
| [`Cases.lean`](IntelliJ/Cases.lean) | three cases from scala/scala, decided by computation: a mis-anchored chain (`MatchWarnings`), the fallback firing where scalac's walk stops (`Importers`), a self-rooted link applied once and twice (`Scanners`), and the shapes of `Relaxations` (D, E) |

```
elan default stable   # Lean 4.34
lake build
```
