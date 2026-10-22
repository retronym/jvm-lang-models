# dotc session x-ray: a toy IDE over the patched `InteractiveDriver`

A web page that calls into the real Scala 3 compiler with [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch) applied (targeted typing with `runUpTo`, a resumable run per file, cancellation that unwinds with `CancelledCompilation`), and shows an x-ray of what the driver did for each request: run id, typed prefix, which top-level statements were typed before / by this request / not at all, where a cancellation unwound, `Run.typedTreeCount` consumed, wall time, and how many symbols of the file are still `Touched` (`isCompleting`) afterwards. Every number is read from the driver; nothing is simulated. Section 5 of [track-i-scala3-cancellation.md](../../../docs/track-i-scala3-cancellation.md) is the design these numbers illustrate.

![the page after the cancel demo](xray.png)

## Files

- [`XrayServer.scala`](XrayServer.scala): a `com.sun.net.httpserver` server (no new dependencies) that owns one `InteractiveDriver` on the presentation-compiler test classpath and one virtual file `A.scala`. `GET /` serves the page, `GET /source` the generated file (60 top-level objects in the shape of `CompletionSessionSuite.bigSource`), `POST /request` runs one request (`complete`: `runUpTo` at the cursor then `Completion.completions`; `full`: `run`) with an optional cancel checker that fires after N ms, and answers with the x-ray as JSON. The driver's `typedTreeCount` is read reflectively so that the compiler patch stays exactly [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch).
- [`xray.html`](xray.html): the page. CodeMirror 5 for the editor and highlight.js for the statement under the cursor, both from cdnjs; the palette and editor theme are borrowed from the viewer of [retronym/greffier](https://github.com/retronym/greffier) (its compile drawer is the natural home for this page later). Three demo buttons: *session* (complete at object 10, 40, 20: the run id stays, the prefix grows then holds), *cancel* (fresh content, complete at object 10, then at object 55 with a 10 ms cancel, then at 55 again: the resume is unwound, the prefix keeps the statements typed before it, the next request resumes the same run), *edit* (type a character, complete: a fresh run).

## Running it

The live copy runs inside a scala3 worktree at `d168df2a76` with [`dotc-session.patch`](../../../../../docs/upstream/dotc-session.patch) applied (`git apply`), with these two files copied to `presentation-compiler/test/dotty/tools/pc/xray/`:

```bash
sbt --mem 8192 -batch "scala3-presentation-compiler/Test/runMain dotty.tools.pc.xray.XrayServer"
```

Then open <http://127.0.0.1:8791/> (`-Dxray.port=...` to change; `-Dxray.page=<path>` if the page is not found relative to the working directory). The first build is about 2.5 minutes; the server warms the driver up on a 5-object file before listening. `Ctrl/⌘-Space` in the editor is "Complete at cursor".
