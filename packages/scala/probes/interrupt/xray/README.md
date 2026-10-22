# dotc session x-ray: a toy IDE over the patched `InteractiveDriver`

A web page that calls into the real Scala 3 compiler with [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch) applied (typing only the path to the request with `runUpTo`, a resumable run per file, cancellation that unwinds with `CancelledCompilation`), and shows an x-ray of what the driver did for each request: run id, which top-level statements are typed and which of their members were skipped, where a cancellation unwound, `Run.typedTreeCount` consumed, wall time, and how many symbols of the file are still `Touched` (`isCompleting`) afterwards. Every number is read from the driver; nothing is simulated. [track-i-dotc-session-design.md](../../../docs/track-i-dotc-session-design.md) is the design these numbers illustrate.

![the page after the cancel story](xray.png)

## Files

- [`XrayServer.scala`](XrayServer.scala): a `com.sun.net.httpserver` server (no new dependencies) that owns one `InteractiveDriver` on the presentation-compiler test classpath and one virtual file `A.scala`. `GET /` serves the page, `GET /source` the generated file (60 top-level objects in the shape of `CompletionSessionSuite.bigSource`), `POST /request` runs one request (`complete`: `runUpTo` at the cursor then `Completion.completions`; `full`: `run`) with an optional cancel checker that fires after N ms, and answers with the x-ray as JSON. The driver's `typedTreeCount` is read reflectively so that the compiler patch stays exactly [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch).
- [`xray.html`](xray.html): the page. CodeMirror 5 for the editor and highlight.js for the statement under the cursor, both from cdnjs; the palette and editor theme are borrowed from the viewer of [retronym/greffier](https://github.com/retronym/greffier) (its compile drawer is the natural home for this page later). Four stories, each stating what the design predicts before a step and checking it against what the driver reported: *session* (complete in object 10, 40, 10 again, then inside `method20`: one run, only the statements at the cursor typed), *cancel, deterministically* (a latched request, see below, cancelled while the typer is blocked, then the same request again), *edit* (a fresh run), *whole file* (`driver.run`, for comparison).
- `tests.macros.Latch` (in the scratch worktree's `presentation-compiler-testcases/src/tests/macros/Latch.scala`, part of the patch): a `transparent inline` macro that blocks the typer while the latch file exists. The generated file's last object has `def giant` whose first statement is `Latch.await`; a "latched" request arms the file, the page shows the typer blocked there with the tree count so far, and *Cancel* or *Release* decides what happens next. This is how a cancellation lands at a known point, deterministically, instead of at whatever the 1,024-tree checkpoint happens to hit.

## Running it

The live copy runs inside a scala3 worktree at `d168df2a76` with [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch) applied (`git apply`), with [`XrayServer.scala`](XrayServer.scala) and [`xray.html`](xray.html) copied to `presentation-compiler/test/dotty/tools/pc/xray/` (the patch carries the latch macro):

```bash
sbt --mem 8192 -batch "scala3-presentation-compiler/Test/runMain dotty.tools.pc.xray.XrayServer"
```

Then open <http://127.0.0.1:8791/> (`-Dxray.port=...` to change; `-Dxray.page=<path>` if the page is not found relative to the working directory; `-Dxray.latch=<file>` enables latched requests, the sbt route sets neither, so for the latch run the server directly: `sbt "export scala3-presentation-compiler/Test/fullClasspath"`, then `java -Dxray.latch=/tmp/xray-latch -cp <that classpath> dotty.tools.pc.xray.XrayServer` from the worktree root). The first build is about 2.5 minutes; the server warms the driver up on a 5-object file before listening. `Ctrl/⌘-Space` in the editor is "Complete at cursor". The page is read from disk on every request, so it can be edited without a rebuild.

## What the numbers were (60 objects, warm JVM)

| request | typed | `typedTreeCount` | ms |
|---|---|---|---|
| fresh completion in object 10, prefix version of the patch | 11 statements whole | 791 | 20–40 |
| fresh completion in object 10, path version | `val r` of object 10 only | 43 | 12–60 |
| resume into object 40 | one more statement | 41 | 7 |
| served from what is typed | nothing | 8 | 1–3 |
| whole file | 60 statements | 12,097 | 357 |
| latched request cancelled inside `giant` | nothing; object 59 re-parsed | 981 before the abort | |
