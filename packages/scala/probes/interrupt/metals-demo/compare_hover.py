"""Hover/definition/completion processing times from Metals' LSP trace, last server start only.
usage: python3 -I compare_hover.py <project-dir>..."""
import sys, re, statistics as st, pathlib
for d in sys.argv[1:]:
    t = (pathlib.Path(d) / ".metals" / "lsp.trace.json").read_text(errors="replace")
    i = t.rfind("Received request 'initialize"); t = t[i:] if i >= 0 else t
    print(f"== {pathlib.Path(d).name}")
    for k in ("textDocument/hover", "textDocument/definition", "textDocument/completion", "textDocument/documentHighlight"):
        v = sorted(int(m.group(1)) for m in re.finditer(rf"Sending response '{re.escape(k)} - \(\d+\)'\. Processing request took (\d+)ms", t))
        if v: print(f"  {k.split('/')[1]:18} n={len(v):4} median={st.median(v):6.0f} p90={v[int(len(v)*0.9)]:6} max={v[-1]:6} ms")
