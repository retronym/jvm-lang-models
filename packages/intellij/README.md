# asSeenFrom, formalized

A small Lean 4 model (no Mathlib) of how scalac computes the type of a selected member, `pre.memberType(m) = info(m).asSeenFrom(pre, owner(m))`, and of IntelliJ's alternative, a chain of substitutor links. Companion to the design note `DESIGN.md` (full design note) and `NOTE.md` (one-page summary with the proposed `ScSubstitutor` assertions), both for retronym/intellij-scala PR #5.

| File | Content |
|---|---|
| `Model.lean` | classes as owner paths, types with this-leaves, a `World` of base-type facts |
| `Scalac.lean` | `thisTypeAsSeen` / `asSeenFrom` by structural recursion (termination for free); P3: results are pieces of the prefix |
| `Chain.lean` | **composition law** `A(p₂,c₂) ∘ A(p₁,c₁) = A(A(p₂,c₂)(p₁), c₁)`; **a chain is one asSeenFrom** (`chain_is_single`); idempotence (I4). Assumes **lockstep**: asSeenFrom commutes with `baseType.prefix`. Then the three structural constraints a runtime assertion can check: **C1** `wellAnchored` (each link anchored at the class of the running composed prefix) ⇒ `chain_is_intended`, the chain views from the *intended* prefix; **C2** `fixedTarget` (a link doesn't rewrite its own target) ⇒ `idempotent_of_fixed`, `dedup`; **C3** `stateSafe` (a substitutor threaded into resolve state has no this-links) ⇒ `stateSafe_preserves_this`, it never re-anchors |
| `IntelliJ.lean` | IntelliJ's walk with the narrow-against-target fallback; `agrees`: it equals scalac's wherever the fallback does not fire |
| `Cases.lean` | case (b) MatchWarnings: mis-anchored vs well-anchored chain, both `decide`d against the single map; case (a) Importers: fallback rewrites where scalac does not |

What is proved: given lockstep, any chain of anchored walks is a single `asSeenFrom` from a composed prefix, and it terminates; the anchor of each link decides *which* prefix. What is not: that `BaseTypes.baseType` satisfies lockstep (an axiom here, checked empirically by the TCK), and termination of IntelliJ's actual engine, which feeds link outputs back into resolution.

```
elan default stable   # Lean 4.34
lake build
```
