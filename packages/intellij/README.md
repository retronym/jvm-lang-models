# asSeenFrom, formalized

A small Lean 4 model (no Mathlib) of how scalac and the IntelliJ Scala plugin compute the type of a selected member, and a proof of the conditions under which they agree. Its consumer is `SubstitutorInvariants` in retronym/intellij-scala#5, which turns each theorem below into a runtime check.

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
| `Chain.compose` | two links in sequence are one link, from the first prefix as seen by the second, provided the first link rewrites every this-type of its input (`inView`) | A5: a this-type on the anchor's owner chain that a link leaves alone is one that scalac's walk also leaves alone |
| `Chain.chain_is_single` | by induction, a whole chain is one `asSeenFrom`, so one pass suffices and no output needs rewriting again | I4: the census that justified deleting the no-self-embedding brake |
| `Chain.chain_is_intended` | if each link is anchored at the class of the prefix composed so far (`wellAnchored`), that one `asSeenFrom` is from the *intended* prefix | A3, A4: measurements, not gates (see link order below) |
| `Chain.idempotent`, `Chain.idempotent_of_fixed` | a link that maps its own target to itself (`hp`) can be re-applied to its own output without effect; `fixedTarget` is a syntactic condition sufficient for `hp` | A1: checks `hp` directly, by applying the link to its target |
| `Chain.stateSafe_preserves_this` | a chain with no this-type rewrites keeps every this-type of its input, so storing it in resolver state cannot re-anchor other references' types | A2: fails the tests if violated |
| `IntelliJ.agrees` | the plugin's walk, fallback included, equals scalac's wherever the fallback does not fire; both start from an anchor | A6: every this-type rewrite has an anchor, now true by construction |

The plugin's scaladocs also use the earlier labels C1, C2, C3 for `wellAnchored`, `fixedTarget`, `stateSafe`.

**Link order.** The model's well-anchored chain has the shape `sig_C >> use`: the signature substitutor of `C` first puts a member declared in a superclass into `C`'s view, then the use-site link, anchored at `C`, views it from the prefix. The plugin builds that order only on some routes (a this-link that arrives through resolve state, after `TypeDefinitionMembers` has put `sig_C` first), and even there anchors the use-site link at `owner(m)`, not at `C`. On the main route, `ScalaResolveState.substitutorWithThisType(owner(m))` *prepends* the use-site link, giving `use >> sig_C`: the use-site link runs first, on the declared type, anchored at the class it was written in, and `sig_C` sees only what it left. Its first link is already scalac's whole map, `asSeenFrom(pre, owner(m))`, but the chain is not the shape `wellAnchored` describes, and A3 and A4 fire on it by the hundreds of thousands. **A3 and A4 measure how far the plugin's chains are from the model's shape; they are not a gate.**

What is not proved: that `BaseTypes.baseType` satisfies lockstep (an assumption here, checked by the TCK), and termination of the plugin's engine as a whole, which feeds link outputs back into resolution. `chain_is_single` says that for chains in the model no output needs re-rewriting, which is what made the brake redundant.

## Files

| File | Content |
|---|---|
| `Model.lean` | classes as owner paths, types with this-leaves, a `World` of base-type facts |
| `Scalac.lean` | scalac's `thisTypeAsSeen` and `asSeenFrom` as structural recursion, so termination is the checker's; `inView` |
| `Chain.lean` | lockstep; `compose`, `chain_is_single`, `idempotent`; then the checkable conditions `wellAnchored`, `fixedTarget`, `stateSafe` and their theorems |
| `IntelliJ.lean` | the plugin's walk with its narrow-against-target fallback; `agrees` |
| `Cases.lean` | two cases from scala/scala, decided by computation: a mis-anchored chain (`MatchWarnings`) and the fallback firing where scalac's walk stops (`Importers`) |

```
elan default stable   # Lean 4.34
lake build
```
