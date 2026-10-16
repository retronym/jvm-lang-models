# Refined plan, 16 October 2026: where the next findings are

A review of the whole effort against three outside references: the bug trackers as they stand today (via the local index of scala/bug, scala/scala3, sbt/zinc, scala-garden/mima and the contributors forum), the talks in retronym/talks, and the Merkle hashing proof of concept in retronym/zinc that started this. It asks four questions of each part of the model: does it find real implementation bugs, does it find specification omissions or contradictions, does it tell us something about the design of our own systems, and does it make the complexity of those systems legible. It ends with a ranked plan and with a short discipline for a compiler practitioner using these tools without being a formal-methods expert.

Facts checked against the tree at `367282b`. Nothing here is implemented.

## 1. Where the method has paid, and why

Every finding of the last ten days came from one of three moves, and it is worth naming them because the plan below is built from them.

**A calibrated executable model, decided by the kernel on a bounded space, held against the real tool.** The Scala membership model found [scala/bug#13199](https://github.com/scala/bug/issues/13199) through its *runtime* check, not its static one: refchecks and the model agreed, HotSpot disagreed. The JVM linkage model found HotSpot's loading order against JVMS §5.3.5, the `invokeinterface` access clause the model lacked, and two JDK bugs on 21, because every program of a space was run on three JDKs. Track T found dotc's unchecked member bounds (a contradiction of SLS §4.3 and a cast-free `ClassCastException`) by compiling and running 2,430 programs. None of these was a theorem about all programs; all were differences between two executable things on an enumerated space.

**A shape taken from the specification's own text, not from a space.** The two JVM model bugs of 12 October (transitive overriding, the final-method check at loading) came from encoding JVMS §5.4.5's worked example, after 88,000 space programs had not reached the shape. The lesson from the next-steps review stands: spaces exhaust a shape quickly; each new shape finds something.

**A theorem whose hypotheses name what a tool must record.** The obligations (`comp`, coverage, abstraction) turned "Zinc missed this" into "the bridge records no key covering this query", which is a sentence a maintainer can act on, and it produced the 20 predicted scripted tests in retronym/zinc. Theorem B4 did the same for binary compatibility and found the MiMa gaps. The theorems earn their keep as a vocabulary and a review checklist; the talks say this too.

The talks also record what did *not* pay: scripted tests that only check which classes recompiled (the Merkle PoC passed the suite with a rule switched off), assuming the clean build is a fixed reference (scalac's output depends on the batch), and harness bugs that masqueraded as findings.

## 2. Where the model confidently says nothing

These are the places where the repository has a definition, a number or a theorem that looks like coverage and is not. Each is also where the trackers are active today.

### 2.1 Compositionality is one bit

`comp` is the obligation the compilers most often fail, and the model's whole account of it is `View.inRun : Bool` in [`Scala.Lower`](../../../packages/scala/Scala/Lower.lean): a declaration is answered either as the typer has it in the same run or as the TASTy reader produces it, and the one modelled difference is `NoInits` (F6). The bug catalogue has 34 compiler rows of this kind, 22 of them gaps, and [`docs/evidence/bug-map.md`](../../evidence/bug-map.md) says the model "should only classify these". Yet this is the most active seam in the trackers right now: [scala/scala3#26551](https://github.com/scala/scala3/issues/26551) (TASTy sharing depends on type identity), [scala/scala3#26552](https://github.com/scala/scala3/issues/26552) (member order and `InnerClasses` under separate compilation), [scala/scala3#27265](https://github.com/scala/scala3/issues/27265) (the F6 shape, filed from this work), [scala/scala3#25974](https://github.com/scala/scala3/issues/25974) (`export` wildcard forwarder order), [scala/scala3#22181](https://github.com/scala/scala3/issues/22181), the umbrella [scala/scala3#7661](https://github.com/scala/scala3/issues/7661), and on the Scala 2 side the TASTy-reader family [scala/bug#13113](https://github.com/scala/bug/issues/13113), [scala/bug#13114](https://github.com/scala/bug/issues/13114), [scala/bug#13122](https://github.com/scala/bug/issues/13122), [scala/bug#13125](https://github.com/scala/bug/issues/13125). The Catalyst differential in the Merkle PoC found six batch dependences in scalac in 146 edits (fixed as [scala/scala#11289](https://github.com/scala/scala/issues/11289) to #11293).

The structural reason is that the model has no notion of *what a pickle carries*. `Iface` is a declaration; the real interface is a TASTy tree or a Scala signature, and every `comp` bug is a fact that the in-run symbol table has and the unpickled one lacks (or has differently): a flag computed by the namer and not stored (`NoInits`), an `InnerClasses` entry only emitted when a type is traversed, a sharing decision keyed on object identity, a symbol order. A model that says what the interface projection *drops* would classify these as one thing and predict more of them.

### 2.2 The bridge's `π` and `keys` are idealised

Every Zinc instance proves its obligations for keys the model defines. None states Zinc's `ExtractAPI`, `HashAPI` or `ExtractUsedNames`; the talks concede that the model never shows scalac or dotc meet the obligations, and abstraction is "perfect hashing by fiat". The empirical substitutes are the conformance harness and the Merkle PoC's `CHECK` mode and Analysis key check (136 uncovered cases on byte-identical builds before the fix in [retronym/zinc#54](https://github.com/retronym/zinc/issues/54)). Coverage, the obligation behind 38 of 145 bugs, is therefore checked only where someone wrote a scripted test.

### 2.3 Precision has no definition

Thirty-five of the catalogued bugs are over-compilation, the user-facing one is [sbt/zinc#1396](https://github.com/sbt/zinc/issues/1396) (400 files on a local rename), and the entire motivation of the Merkle PoC is precision. The framework proves soundness and says "precision is proved per instance", which in practice means it is not stated. The talks admit the PoC's wins are benchmark tables on a noisy machine. Without a definition, the Lean model cannot say whether `DescendantRules.default` is better than `all` on any space, only that both are sound.

### 2.4 Failing rounds do not exist

`group` is total. The largest remaining Zinc gap cluster (K-SM in the bug map: [sbt/zinc#476](https://github.com/sbt/zinc/issues/476), #535, #598, and the retry [sbt/zinc#1780](https://github.com/sbt/zinc/issues/1780) with five pending scripted tests) is about a round that *fails* because a unit was compiled against a stale interface, and a policy that reads that failure. Zinc's maintainers are weighing #1780 now; the model has nothing to say about whether its retry is sound or terminates.

### 2.5 The Scala type model is narrow where the soundness bugs are

`Members` is a method `m` with result `String` or `Int` over four classes; Track T's first space is two traits with one type member. The open soundness issues cluster elsewhere: match types ([scala/scala3#27113](https://github.com/scala/scala3/issues/27113), [scala/scala3#20189](https://github.com/scala/scala3/issues/20189), which is unsound *only under separate compilation*, [scala/scala3#24760](https://github.com/scala/scala3/issues/24760)), initialisation ([scala/scala3#23061](https://github.com/scala/scala3/issues/23061), [scala/scala3#11572](https://github.com/scala/scala3/issues/11572)), union types with `TypeTest` ([scala/scala3#22950](https://github.com/scala/scala3/issues/22950)), by-name defaults in enum constructors ([scala/scala3#23213](https://github.com/scala/scala3/issues/23213)), and, two weeks old, projection on a wildcard-applied trait with conflicting bounds ([scala/scala3#27211](https://github.com/scala/scala3/issues/27211)), which is exactly the second space Track T planned and had not built.

### 2.6 The lowering is calibrated on one version of each compiler

`Scala.Lower` agrees with 2.12.21, 2.13.18 and 3.9.0 on every program. It says nothing about 3.3 LTS, 3.8, or the next RC, and the trackers show that the compiler's own releases are the largest source of binary breaks users meet: [scala/scala3#26800](https://github.com/scala/scala3/issues/26800) (3.9.0-RC5 dropped `$init$` for a trait holding only a nested object; Play broke; the cause was one line, `case _: ModuleDef => NoInits`), [scala/scala3#24553](https://github.com/scala/scala3/issues/24553) and [scala/scala3#24671](https://github.com/scala/scala3/issues/24671) (3.8.0 RCs, exported `val`s and `copy` default getters), [scala/scala3#24581](https://github.com/scala/scala3/issues/24581) (generic signatures), [scala/scala3#27063](https://github.com/scala/scala3/issues/27063) (3.3.9-RC1 against Pekko), and on Scala 2 [scala/bug#12961](https://github.com/scala/bug/issues/12961) and [scala/bug#13183](https://github.com/scala/bug/issues/13183). Each was found by a downstream project's MiMa run, after the RC. The `hasInit` rule in `Lower.lean` is precisely the rule #26800 changed, and the model, calibrated after RC5, encodes the new behaviour without knowing the old one existed.

### 2.7 Names

Track N's design brief says it: private name expansion, super accessors, outer fields, lambda numbering, default getters, lazy-val encodings, `inline$` and `$proxy` are absent, and these are where source-invisible edits become binary ones. [scala/scala3#26445](https://github.com/scala/scala3/issues/26445) and [scala/scala3#25593](https://github.com/scala/scala3/issues/25593) (Scala 2 and 3 disagree on erasure of type members and on nested-class construction) are 2-versus-3 encoding differences that a `Dialect` table would state.

## 3. Where the model says something irrelevant, or at a cost not worth paying

- **The port of the Zinc toys onto the shared Scala layer** (roadmap mountain 5) is coherence work. It has found two `Members` gaps through `FlatShared`, which is the argument for it, but the remaining step (`Erasure`'s two-parameter walk) and the implicit-scope restatement are unlikely to find anything the probes have not. Do it only when a finding needs it.
- **The general soundness proof for `Fixed`** is worth having for upstreaming, but the maintainers' response to the four MiMa issues will tell us whether a proof moves them. Write the statement; defer the proof until a maintainer asks.
- **`MiMa.Sound` at an hour and 9 GB** is a kernel `decide` over 149 edits times the client space. The result is a calibration number; the hour is paid on every change to `Fixed`. A smaller space with the same witnesses would serve the ledger as well.
- **The 20/20 predictions** should be stated more carefully in any narrative: one is a termination property, three restate an already-fixed family, and the bug map's "predicts yes" is counterfactual for most phases (the instance was built after the bug). The honest number is the eight to ten findings that were new to their trackers, and that number is good.
- **Theorems for every program on [`XCompiler`](../../../packages/inc-comp/IncComp/General.lean#L22)** (the mixed explicit/inferred T3b, file-level T4) are mathematics the Zinc maintainers will not read. They matter only if a policy decision rests on them; #1780 is the first that does.

## 4. Prior art: patterns that mined rich seams, and their analogues here

What the productive mechanisation efforts have in common is that the formal artefact was a *second executable* held against the first, and the bugs were found by the comparison, not by the proof. The proof's value was to make the second executable trustworthy and its hypotheses explicit.

| Pattern | Where it paid | The analogue in this repository |
|---|---|---|
| Differential testing of the real tool against an executable semantics, at scale | Csmith: no wrong-code bug in CompCert's verified middle end, 79 in GCC and 202 in LLVM, and about six in CompCert's *unverified* edges (front end, assembler printing), which Leroy then moved inside the proof ([Yang et al. 2011](https://users.cs.utah.edu/~regehr/papers/pldi11-preprint.pdf)); Alive2 run over LLVM's own unit tests, 47 miscompiles at publication and over 50 since ([Lopes et al. 2021](https://www-old.cs.utah.edu/~regehr/alive2-pldi21.pdf)); YARPGen and EMI, hundreds more | The probes and the compile server. Scale them across *versions* (§5.1) and across *compilation groupings* (§5.2); the differences are the bugs, and the model's job is to say which rule each one is. |
| Replay the project's own test corpus through the model | The GraalVM optimiser in Isabelle ran 2,544 of GraalVM's unit tests through the model and found arithmetic model bugs and an off-by-one in stamp refinement that the tests themselves had hidden ([Webb et al. 2022](https://arxiv.org/abs/2212.01748)); Alive2 above | dotc's `tests/pos` and `tests/neg`, scala/scala's partest, Zinc's scripted tests and MiMa's own test corpus are shape generators nobody has pointed at the models (§5.3). |
| The specification as an executable artefact, with the prose checked against it | WebAssembly: Watt's Isabelle mechanisation during drafting found spec errors that were adopted; SpecTec now generates prose, rules and an interpreter from one source and caught 7 historical errors and 10 in pending proposals ([Youn et al. 2024](https://dl.acm.org/doi/10.1145/3656440)); ESMeta for ECMAScript, 27 spec bugs and 44 engine bugs from one mechanised spec ([Park et al. 2021](https://arxiv.org/abs/2102.07498)); K-Java's fixes adopted into later JLS editions | The specification ledger and the literate pages. Next: the ledger's `unspecified` entries as probe inputs, and JLS chapter 13 clause by clause (§5.7). |
| Completeness, not only soundness | MetaCoq's correct *and complete* checker found an incompleteness in Coq's kernel, fixed in 8.14 ([Sozeau et al. 2024](https://rocq-prover.org/papers/correct-and-complete-type-checking-and-certified-erasure-for-coq-in-coq)) | `Members` already checks both directions (the accepted sets agree exactly). State it as the rule for every calibrated check: "model rejects, compiler accepts" is a soundness lead; the reverse is a specification gap. |
| Lookups recorded as the dependency, misses included | Kotlin's `LookupTracker`; the build-systems-à-la-carte trace, whose Coq and Agda mechanisations sharpened the correctness criterion rather than finding implementation bugs ([Forward build systems, formally](https://arxiv.org/abs/2202.05328)) | The coverage obligation. What is missing is the recorder in the real compiler (§5.4). |
| Counterexample-guided revision, with the counterexample kept as a named exclusion | Alive2's known-unsound list; Amin and Tate's DOT counterexamples; Bonsai, which rediscovered [scala/bug#9633](https://github.com/scala/bug/issues/9633) by enumeration; the 2019 covariant-GADT unsoundness found in both scalac and dotc by extending the calculus one feature at a time ([Parreaux et al.](https://arxiv.org/abs/1904.07298)) | `bug13199`, `lowerGap`, [`accepted_sound_except`](../../../packages/scala-types/ScalaTypes/PathsOracle.lean#L68). The right register for a model that is calibrated, not verified. |
| A second, independent implementation of the checker, plus adversarial search | Lean4Lean (a complete re-implementation of Lean's kernel) found one soundness bug; an AI-assisted search in 2026 found six more, with the independent checker nanoda unaffected | tasty-query is an independent TASTy reader; cross-checking it against dotc's unpickler on the lowering space is a cheap second implementation (§5.2). |
| Triage by method | Axon (Lean, 2026): of nine compiler bugs, three fell to testing, three to translation validation with cheap certificates, three only to a failed proof ([Rinard 2026](https://arxiv.org/abs/2605.01660)) | Probes for the common case, kernel `decide` on spaces for the rule, theorems for the long tail a maintainer's decision waits on (§5.8). |

Two cautions from the same survey. A 2026 study of 30 rustc soundness bugs found that cross-version differential testing misses bugs that persist across versions, and that none of RustBelt, Chalk or a-mir-formality could express them; the authors ask for a mechanised spec as the type-soundness oracle ([arXiv 2608.28713](https://arxiv.org/abs/2608.28713)). So §5.1 finds *changes*, and the calibrated model is what finds what every version gets wrong. And nobody has mechanised the JVMS verifier or linker in a modern assistant since Jinja; the JVM layer here is, as far as the survey could find, the only current executable model of JVMS chapter 5 held against HotSpot, which is an argument for publishing it on its own.

The pattern that does *not* transfer is the one most associated with proof assistants: proving an entire compiler correct. CompCert and CakeML took decades and a fixed source language; scalac is neither. The repository's framing (models calibrated against the tool, hypotheses that name what the tool must record) is the right adaptation, and §5 keeps to it.

## 5. The plan, ranked by expected findings per week

Each item says why, what done looks like, what it costs, and what it is likely to find. The first four are new seams; the rest sharpen existing ones. Items 1, 2 and 3 need no new Lean beyond the probe drivers and a translator.

### 5.1 The lowering model as a cross-version binary-compatibility oracle

**Why.** §2.6: the compilers' releases break binary compatibility, and nobody finds it until a downstream MiMa run after the RC. `Scala.Lower` plus the probe plus the compile server is a per-program classfile oracle that costs milliseconds per compile. Running the existing 1,363 programs (and the S6 families, and `FlatRules`' 48,000) through 3.3.x, 3.7.x, 3.8.x, 3.9.0 and the current nightly, and diffing the classfiles' *linkage-relevant* projection (header, members, flags, `InnerClasses`, invokes of synthesised bodies) per program across versions, lists every binary change the compiler team shipped or is about to ship, with a minimal program for each. #26800 would have been one line of that diff between RC4 and RC5.

**Done looks like.** `probe.py --versions` with the compile server started once per version; a report per pair of versions: programs whose projection differs, grouped by the kind of difference; the model's rule for each (so each row says which `Dialect` branch would need a version parameter); the ones that break an old client under `Jvm` linkage marked. The first run is a table in `track-s.md` and a calibration-ledger line; recurring, it is a nightly against the Scala 3 nightly, which is the "CI canary" the incrementality talk asks for. Each confirmed break is an upstream issue before the RC, with the reproducer the probe already prints.

**Cost.** Two to three sessions. The server already pins versions through coursier; the work is the per-version loop and the diff report. The Scala 2 side (2.13.17 against 2.13.18, `-Xsource:3-cross`) is the same loop.

**Expected.** Several real binary differences between 3.3 LTS and 3.9 on the existing space (the trackers show `$init$`, default getters, forwarders for exported members, generic signatures move between minors); a list of which the Scala 3 team considers intended. A calibrated table of 2.12 versus 2.13 versus 3 encodings for the same source, which the migration guide states only in part. This also pins down what "binary compatible across the 3.x line" means in terms of the model's rules, which is a design insight for the compiler team as much as a bug list.

### 5.2 Compositionality as what the pickle drops

**Why.** §2.1. The `comp` rows are the largest unmodelled class, the most active in the trackers, and the ones the Merkle PoC's bridge-side hashing depends on (bridge hashes are computed from the in-run tree; the next build's are from TASTy). A model of the interface projection, `pickle : InRunDecl → Iface`, with the facts it drops listed explicitly (namer-computed flags, traversal-dependent attributes, sharing, order), turns "joint ≠ separate" from a classification into a prediction: any lowering rule that reads a dropped fact is a `comp` failure.

**Done looks like.** Three steps. (a) A probe, not Lean: for every program of the lowering space, compile each class alone against the others' TASTy, and diff the projection against the joint build; the same for Scala 2 pickles. This is `DeterminismTest` across groupings instead of across runs, on 1,363 programs instead of the compiler's test corpus, and it finds the shapes. (b) `Lower`'s `View` gains the fields the probe shows are dropped, each a `Spec: unspecified` entry (the SLS does not define TASTy) and a witness by kernel `decide` in `Scala.Facts`. (c) The Zinc side: [`ZincBridgeScala3.not_comp`](../../../packages/links/Links/ZincBridgeScala3.lean#L79) generalised from F6 to "any rule reading a dropped field", so the obligation names the fix: store the fact in the pickle, or recompute it in the reader as [retronym/scala3#10](https://github.com/retronym/scala3/issues/10) does for `NoInits`.

**Cost.** Step (a) is a session with the compile server (it already supports a classpath of earlier outputs, with a fresh instance). Steps (b) and (c) are a session each per shape found.

**Expected.** New `comp` shapes beyond F6 on the existing space; a list of TASTy fields that are recomputed rather than stored, which is a design document the Scala 3 team does not have; and the scalac side (Scala signatures) for the 2.13 TASTy reader bugs. For Zinc, it is the precondition for trusting bridge-side hashing in the Merkle design.

### 5.3 Replay the compilers' own test corpora through the models

**Why.** The GraalVM and Alive2 experience: a project's own tests are the densest collection of shapes its authors thought mattered, and running them through a model finds both model bugs and the cases the tests silently got wrong. dotc's `tests/pos` and `tests/neg` hold thousands of programs, many of them minimised bug reports; the subset within `Members`' and `Paths`' syntax (classes, traits, objects, `def`/`val`/`lazy val` members, type members with bounds, no bodies that matter) is extractable by a parser that rejects anything else. MiMa's own test suite (`functional-tests`) is a catalogue of library edits with expected problems, which the MiMa model and `Fixed` can be run over directly, and it is the corpus the maintainers trust.

**Done looks like.** A filter that admits a test file when it is within a model's language, a translator into the model's AST, and a run: for `Members`, agreement on accepted/rejected and on the owner that runs; for `Paths`, the soundness verdict; for MiMa, the problem list against the test's expectation and against HotSpot. Every disagreement is triaged as model gap, test expectation wrong, or compiler bug. **Cost.** Two sessions for the filter and translator per corpus; the runs are minutes on the server. **Expected.** A list of model gaps ranked by how often real tests hit them, which is a better prioritisation of the layer remainders (type members, `var`, overloading, Java parents) than the roadmap's guesswork; and some test expectations that are wrong, which happened to GraalVM and is the kind of finding maintainers like.

### 5.4 Coverage checked in the real compiler: a lookup trace

**Why.** §2.2. Coverage is assumed per instance and checked by scripted tests. The talks' own open list has "log queries from the real compiler to check coverage"; Kotlin does this in production. A compiler plugin (Scala 2: a phase after typer that wraps `Scope.lookup`, `Type.member`, `Symbol.info` completion, implicit search candidates; dotc: the same through `Denotations` and `Implicits`) that records every lookup with its scope, hit or miss, and a checker that compares the recorded set against the keys Zinc's Analysis stores for the unit, gives coverage as a per-compile check on any codebase, not only on the model's spaces. The [retronym/zinc#54](https://github.com/retronym/zinc/issues/54) key check did this for one key kind on one corpus and found 136 misses.

**Done looks like.** The plugin, the trace format (unit, query kind, scope, name, result), the checker against `Analysis`, and a run over Zinc's scripted tests and one real project (catalyst, since the differential harness is there). Every uncovered lookup is either a known family (named in the bug map) or a new one. The model's `keys` for the relevant instance is then checked against what the bridge *actually* records, which closes the gap the talks name.

**Cost.** Three to four sessions; the Scala 2 half is easier (one `Global`, the TCK's reference engine is the template). This is tooling, not Lean, and it is the single piece that would let a Zinc maintainer run the obligation on their own build.

**Expected.** New coverage misses on real code (the predicted-variant list in the bug map has eleven shapes nobody has tested); a measured over-approximation of today's name hashing, which is precision data for free; and the empirical half of the Merkle bridge-hashing argument.

### 5.5 Precision as a theorem and a number

**Why.** §2.3 and the Merkle PoC, whose rule table "is complete only by testing" and whose wins are unmeasured in the model. The definition is already in prose in [`docs/specification.md`](../../specification.md): per edit, units whose keys changed minus units whose traced answers changed. Stated once on [`XCompiler`](../../../packages/inc-comp/IncComp/General.lean#L22) as `overInvalidated`, with the two theorems that follow (a key with a smaller `covers` over-invalidates less; two sound designs compared by inclusion), the conformance dumps and the exhaustive spaces give the number per design.

**Done looks like.** The definition and the inclusion theorem in [`General.lean`](../../../packages/inc-comp/IncComp/General.lean); a per-instance `example` giving the over-invalidation on its space for today's keys and the fix; `Flat`'s `DescendantRules` presets (`all`, `default`, `strict`) compared on `FlatRules`' 216,000 configurations by kernel `decide`, which is the number the PoC's design table lacks. Then the harness: `lake exe conformance` already emits recompiled sets per edit; subtract the model's affected set and report.

**Cost.** One session for the framework, one per instance worth measuring. **Expected.** A design insight more than a bug: which of the PoC's rules buys what, on a space where the answer is exact, and whether `uses` and `fallbacks` are redundant for the reason the PoC claims (assumption 2 in its plan) or only on its corpus.

### 5.6 Track T's second space, now

**Why.** §2.5. [scala/scala3#27211](https://github.com/scala/scala3/issues/27211) is the projection-plus-wildcard shape Track T's design listed for its second space, filed two weeks ago by someone else. The infrastructure (generator, oracle, kernel-decided theorem with named exclusions) is built and found one contradiction on the first space. The second space adds projection `T#L`, class type parameters in bounds, wildcards, and `lazy val` and field paths under `-source future`; the third adds match types, where three open unsoundness issues sit and one of them ([scala/scala3#20189](https://github.com/scala/scala3/issues/20189)) is a `comp` failure, so it also feeds §5.2.

**Done looks like.** The space, the five compiler settings, the theorem with exclusions, the ledger entries, and a tracker issue for each new exclusion. **Cost.** Two sessions for the second space; match types are a model extension of their own.

**Expected.** More cast-free `ClassCastException`s, because the first space found one on its first run and the trackers show the family is open; and a statement of which checks (`CheckRealizable`, volatility, `checkGoodBounds`) close which shapes, which is what a fix needs.

### 5.7 JLS chapter 13 audited clause by clause

**Why.** The specifications review ranked it third and called it mechanical; it has not been started beyond 20 examples. Chapter 13 has about sixty "binary compatible" and "not binary compatible" claims, the Java catalogue and `Jvm` linkage can decide each, and the model already found that the JLS says when an edit is an error but not what happens otherwise. Where the JLS says compatible and the JVMS makes it fail to link (or the reverse) is a contradiction between two specifications of the same platform, which is the rarest and most citable kind of finding.

**Done looks like.** One `example` per claim in [`Jls13.lean`](../../../packages/java/Java/Jls13.lean), tagged for the ledger; the claims the catalogue cannot express listed as Java-layer remainders. **Cost.** Two sessions. **Expected.** A handful of omissions ("otherwise" cases) and at least one contradiction around default methods and `invokeinterface` access, where the JVMS clause the model lacked until Track J7 lives.

### 5.8 Failing rounds and the bridging-classes retry

**Why.** §2.4. [sbt/zinc#1780](https://github.com/sbt/zinc/issues/1780) is an open policy proposal with five pending tests behind it, and the model cannot judge it because `group` cannot fail. The extension is a `Task` whose output may be a failure when an answer came from a stale interface, `comp` restated on partial groups, and a `Policy` that reads the failure. Then #1780's retry is a policy, and the questions are soundness (T3a with retries) and termination (does the retry re-enter the ping-pong?).

**Done looks like.** The extension in `inc-comp`, #598 and #535 as witnesses, #1780's policy with its theorem or counterexample, and a comment on the PR with the result. **Cost.** Two to three sessions of Lean; the first theorem work on this list that a maintainer's decision waits on.

### 5.9 Track N, steps 1 and 2 only

**Why.** §2.7. The design brief is reviewed; the first two steps (structured names over what the lowering already emits; private expansion and accessors) are where MiMa false positives and the 2-versus-3 differences are. Steps 3 to 5 can wait for a finding that needs them. **Cost.** Two sessions. **Expected.** MiMa reports on expanded names classified as gap, false positive or right; the 2-versus-3 name table.

### 5.10 Class initialisation

**Why.** `<clinit>` and constructor order are the one JVM mechanism the catalogue mutes (the probe disables static initialisers), the Scala `$init$` chain already lives in the model's bodies, and two open soundness issues ([scala/scala3#23061](https://github.com/scala/scala3/issues/23061), [scala/scala3#11572](https://github.com/scala/scala3/issues/11572)) and dotc's safe-init checker are about initialisation order. Specifications review question 7. **Cost.** Three sessions after Track J4's bodies; it needs `<clinit>` triggering (JVMS §5.5) and a notion of a field read before its write. Lower on this list because the first six items are cheaper per finding.

## 6. A discipline for using these tools, for a compiler practitioner

These are the rules the last ten days support, stated so they can be applied without judgement calls about Lean.

1. **Start every seam with a probe, not a definition.** Enumerate programs, compile and run them with the real tools, diff. If the diff is empty, the seam is closed and no model is needed. The model comes second, to say *which rule* explains the diff and to decide the rest of the space by the kernel. §5.1, §5.2 (a) and §5.3 are probes alone.
2. **Shape before space.** When a space agrees with the tool everywhere, encode a worked example from the specification, a bug report's minimised program, or a tracker issue's shape before enlarging the space. The trackers are a shape generator; the local index makes them searchable by mechanism.
3. **Run it, don't reason about it.** Every finding that mattered had a runtime oracle (HotSpot, `main`, a `Throwable`). A static-only calibration (refchecks agrees) found nothing on its own.
4. **A theorem must change a decision.** Write one when a maintainer, a PR or a design table waits on the answer (B4 for MiMa, #1780 for Zinc, the precision inclusion for the Merkle rule table (§5.5)). Otherwise an `example` by kernel `decide` on the space is the right register, labelled as such.
5. **Name every counterexample and keep it.** `bug13199`, `lowerGap`, the JDK 21 deviations. A theorem with named exclusions is more useful than a weaker theorem with none, because the exclusions are the findings.
6. **Calibrate against several implementations and several versions, not one.** One version gives agreement; two give a difference, and a difference is either a bug, a change the vendor did not announce, or a specification omission. The compile server makes versions cheap.
7. **State what the model does not carry, as data.** `Spec: unspecified` tags, the "not modelled" header lines, and the proposed `pickle` drop list are the model's own account of its blind spots. They are also where the next finding is, so keep them generated and current rather than in prose.
8. **Count honestly.** Prefer "found and filed before anyone else" to "predicted". The bug map's counterfactual "predicts yes" is fine as a coverage metric and misleading as a claim.
9. **Prefer finishing a probe loop to porting a toy.** Coherence work (shared layers, framework generalisations) is worth doing when a finding needs it, and is a sink otherwise.

## 7. Suggested order

§5.1 first (two sessions, no Lean, immediate upstream value, and it exercises the compile server across versions, which §5.2 and §5.6 need). Then §5.2 (a) and §5.6 in parallel, since one is a probe and the other a space. §5.3 beside them, since its translator is independent work and its output re-ranks the layer remainders. §5.5 next, because it is small and unblocks evaluating the Merkle rules, which is the question this repository was created to answer. §5.4 is the largest tooling item and the one with the most durable payoff for Zinc; start its design note after §5.1's first run. §5.7, §5.8, §5.9 and §5.10 as the sessions allow, in that order.

The upstream queue (six drafts in [`docs/upstream`](../../upstream/README.md), the Zinc tests in retronym/zinc) stays as the specifications review left it: a few at a time, and each finding from §5.1 joins it with its reproducer.
