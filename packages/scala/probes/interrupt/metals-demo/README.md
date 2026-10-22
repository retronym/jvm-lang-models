# The session spike under Metals

A sample project for the dotc session spike ([retronym/scala3#68](https://github.com/retronym/scala3/pull/68)) and a way to drive Metals on it without an editor. The design doc's [integration section](../../../docs/track-i-dotc-session-design.md#7-integrating-the-poc-into-a-metals--vs-code-workflow) has the steps: publish the patched compiler locally (version `3.10.2-RC1-bin-SNAPSHOT`), open this folder with Metals, read `.metals/metals.log` for the `[dotc-session]` line each request prints under `-Yinteractive-log`.

- [`build.sbt`](build.sbt): the Scala version of the local publish and the log option. The source is the x-ray's generated file (`curl http://127.0.0.1:8791/source`), with the latch macro replaced by `0`.
- [`metals_lsp.py`](metals_lsp.py): a minimal LSP client. `python3 -I metals_lsp.py <metals launch command...> -- <project dir> src/main/scala/A.scala 43:40 163:40` initializes Metals on the project, opens the file, sends completion, hover, definition and signature help at each position, and prints the `[dotc-session]` lines from the log.
- [`build-dotc-snapshot.sbt`](build-dotc-snapshot.sbt): the build of a second project whose sources are the x-ray's snapshot of `compiler/src/dotty/tools/dotc` (copy the snapshot under `src/main/scala`), typed against the published compiler as a library.
