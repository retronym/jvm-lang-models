# Phase records

One record per phase of the Zinc model from phase 10 on: the question, what the compiler reads, the design, and the results. Phases 1 to 9 are in `docs/history/phases.md` at the repository root; what each phase proved and checked is in `docs/status.md`.

`28-sam.md` is the template for a new feature.

| phase | topic |
|---|---|
| 10 | [name resolution, mechanically](10-names.md) |
| 11 | [Scala 3 `inline` and opaque types](11-inline.md) |
| 12 | [Java in mixed builds: name resolution and sealed hierarchies](12-java.md) |
| 13 | [name resolution across subprojects](13-split.md) |
| 14 | [compile order and pipelining: a Java unit's two interfaces](14-order.md) |
| 15 | [inferred types in a cycle: T3a holds, T3 fails](15-cycles.md) |
| 16 | [class-name agreement between the bridge and Zinc](16-naming.md) |
| 17 | [hash stability across forms: source, pickle, classfile](17-hash.md) |
| 18 | [annotations as API and as dependencies](18-annotations.md) |
| 19 | [pipelining's early-output lifecycle](19-pipelining.md) |
| 20 | [constructors and synthetic case-class members](20-synthetic.md) |
| 21 | [derived API: export forwarders and used types' supertypes](21-derived.md) |
| 22 | [Scala 3 macro dependencies: what an expansion reads, when it is recorded](22-macros.md) |
| 23 | [the extraHash lineage and the companion namespace](23-extrahash.md) |
| 24 | [member selection through extensions](24-extensions.md) |
| 25 | [companion pairs in a hierarchy space](25-companions.md) |
| 26 | [Files as a layer](26-files.md) |
| 27 | [import selectors and Scala 3.7's given prioritisation](27-imports.md) |
| 28 | [SAM conversion and local classes](28-sam.md) |
