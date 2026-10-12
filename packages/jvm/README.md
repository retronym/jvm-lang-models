# `Jvm`

When does a classfile link against a library, and to which method? JVM linkage (JVMS §5.4: resolution, selection, access) as a `Task` over the class table, so a library edit that agrees with the old library on a client's linkage footprint links it the same way ([`link_congr`](Jvm/Link.lean#L705)). No Mathlib.

**Start here.** [`Jvm/Link.lean`](Jvm/Link.lean), then [`Jvm/Catalogue.lean`](Jvm/Catalogue.lean).

**Calibration.** `probes/` renders the catalogue with the Classfile API and runs each client on HotSpot 21, 25 and 27: every program of the client spaces agrees ([sizes](../../docs/stats.md#jvm-catalogue-and-client-spaces)), except where they hit two known JDK 21 bugs (JDK-8356942, JDK-8350029). [`docs/track-j.md`](docs/track-j.md).

**Gaps.** Method bodies are their linkage behaviour only, with no data or control flow (Track J4); class initialisation and smaller linkage gaps ([`docs/roadmap.md`](../../docs/roadmap.md) at the repository root).

## Files

| File | Contents |
|---|---|
| [`Jvm/Link.lean`](Jvm/Link.lean) | JVM linkage (JVMS §5.4) as a `Task` over the class table; T1 as [`link_congr`](Jvm/Link.lean#L705) |
| [`Jvm/Catalogue.lean`](Jvm/Catalogue.lean) | Library edits with a client; the outcome before and after by kernel `decide`, with MiMa's problem |
| [`Jvm/Clients.lean`](Jvm/Clients.lean) | Bounded client spaces: does an edit break some client? |
| [`Jvm/Dump.lean`](Jvm/Dump.lean) | Catalogue cases as JSON for `probes` |
| `probes/` | `probe.sh` renders `jvmcases` with the Classfile API (`Render.java`, JDK 24+) and runs each client on HotSpot (`Run.java`, `ProbeLog.java`, `Json.java`); `Instrument.java` adds `ProbeLog` calls to a compiler's classfiles |
