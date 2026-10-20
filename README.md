# Lean models of the JVM, Java, Scala, incremental compilation, Zinc, MiMa and IntelliJ

**[retronym.github.io/jvm-lang-models](https://retronym.github.io/jvm-lang-models/)**: the layers and what each can do for you, the [literate pages](https://retronym.github.io/jvm-lang-models/literate/) and the [API documentation](https://retronym.github.io/jvm-lang-models/api/).

Lean 4 models of the tools that build JVM languages: when a classfile links, what javac, scalac and dotc emit, when an incremental build equals a clean one, what Zinc, MiMa and the IntelliJ Scala plugin get right and wrong. Each layer answers one question and is calibrated against the real tool before anything is built on it. The Zinc model's hypotheses are the point: they are the specification a compiler bridge must meet. Nothing here verifies scalac; the models are calibrated against it.

```bash
lake exe cache get && lake build
```

Lean and Mathlib `v4.34.0`. `lake build` builds `All`, every library except `MiMa.Sound` (about 45 minutes) and `Scala.Refchecks` (about 20). The site is [`site/index.html`](site/index.html), the literate pages [`literate/`](literate/) (`lake exe literate --output _out` there), the API documentation [`docbuild/`](docbuild/) (`lake build All:docs`); the [`Pages`](.github/workflows/pages.yml) workflow publishes them.

## Packages

Each has a README with its question, where to start, its calibration and its gaps. Imports go one way: the core layers never import a consumer. Each also has a `Spec` module (`Query.Spec`, `Zinc.Spec`, …) stating its key definitions and theorems in prose, each name checked by the build. The Mathlib-free ones can be required on their own by `git … subDir`, as the TCK does with [`packages/intellij`](packages/intellij). Sizes: [`docs/stats.md`](docs/stats.md).

| package | question | Mathlib |
|---|---|---|
| [`query`](packages/query/README.md) | a computation that asks questions, and why its trace is enough (T1) | no |
| [`jvm`](packages/jvm/README.md) | when a classfile links, and to which method | no |
| [`java`](packages/java/README.md) | what javac emits; JLS chapter 13 | no |
| [`scala-types`](packages/scala-types/README.md) | `asSeenFrom`, resolution, membership, as scalac computes them | no |
| [`scala`](packages/scala/README.md) | what scalac and dotc emit | no |
| [`intellij`](packages/intellij/README.md) | when the IntelliJ plugin's substitutor chains agree with scalac | no |
| [`inc-comp`](packages/inc-comp/README.md) | when an incremental build equals a clean one, for any compiler and policy | yes |
| [`zinc`](packages/zinc/README.md) | Zinc's loop, bridges and features as instances | yes |
| [`mima`](packages/mima/README.md) | what MiMa reports and misses; corrected rules | yes |
| [`links`](packages/links/README.md) | B4: Zinc-clean implies binary-compatible | yes |
| [`harness`](packages/harness/README.md) | executables and scripts that drive the calibration | yes |

## Where next

- [`docs/README.md`](docs/README.md): where to start by goal, and every document by what it is for.
- [`docs/theorems.md`](docs/theorems.md): the obligations and T1–T5, where their hypotheses bite, and the trust checks (no `sorry` or `axiom`; `native_decide` only in `example`s; core theorems on the standard axioms, checked in CI).
- [`docs/status.md`](docs/status.md): what is proved, what is checked, and the bug map's counts.
- [`docs/findings.md`](docs/findings.md): what the models found in scalac, dotc, Zinc, MiMa and HotSpot that needs triage, and what was decided.
