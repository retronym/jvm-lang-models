"""Interleave edits and hovers against Metals over stdio: for each step, append a space to a body line
(didChange, full text), wait `gap` ms, hover at a position on another line; print round-trip times.
usage: python3 -I edit_replay_lsp.py <metals launch...> -- <project-dir> <edit-sequence.json> <out.json> [gap_ms]"""
import json, os, subprocess, sys, threading, time, pathlib, re
args = sys.argv[1:]; sep = args.index('--'); cmd, rest = args[:sep], args[sep + 1:]
proj = pathlib.Path(rest[0]).resolve(); seq = json.load(open(rest[1])); out = rest[2]; gap = int(rest[3]) / 1000 if len(rest) > 3 else 0.15
src = proj / "src/main/scala/dotty/tools/dotc"; log = proj / ".metals" / "metals.log"
p = subprocess.Popen(cmd, cwd=proj, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=open(str(proj / "metals-stderr.log"), "wb"))
seqn = 0; pending = {}; lock = threading.Lock()
def write(msg):
    data = json.dumps(msg).encode()
    with lock: p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data); p.stdin.flush()
def send(method, params, req=True):
    global seqn
    msg = {"jsonrpc": "2.0", "method": method, "params": params}
    if req: seqn += 1; msg["id"] = seqn
    write(msg); return seqn if req else None
def reader():
    while True:
        line = p.stdout.readline()
        if not line: return
        if line.lower().startswith(b"content-length:"):
            n = int(line.split(b":")[1]); p.stdout.readline(); body = json.loads(p.stdout.read(n))
            if "id" in body and "method" not in body: pending[body["id"]] = (time.perf_counter(), body)
            elif "method" in body and "id" in body:
                m = body["method"]; result = None
                if m == "window/showMessageRequest":
                    acts = body["params"].get("actions") or []
                    result = next((a for a in acts if re.search(r"import|start|yes|ok", a.get("title", ""), re.I)), acts[0] if acts else None)
                elif m == "workspace/configuration": result = [{} for _ in body["params"]["items"]]
                write({"jsonrpc": "2.0", "id": body["id"], "result": result})
threading.Thread(target=reader, daemon=True).start()
def wait(i, timeout=300):
    t0 = time.time()
    while i not in pending:
        if time.time() - t0 > timeout or p.poll() is not None: return None
        time.sleep(0.001)
    return pending.pop(i)
i = send("initialize", {"processId": os.getpid(), "rootUri": proj.as_uri(), "capabilities": {"textDocument": {"hover": {"contentFormat": ["markdown"]}}}, "initializationOptions": {"statusBarProvider": "off", "isExitOnShutdown": True}})
wait(i, 120); send("initialized", {}, False)
texts, versions = {}, {}
def open_file(f):
    texts[f] = (src / f).read_text().split("\n"); versions[f] = 1
    send("textDocument/didOpen", {"textDocument": {"uri": (src / f).as_uri(), "languageId": "scala", "version": 1, "text": "\n".join(texts[f])}}, False)
open_file(seq[0]["file"])
t0 = time.time()
while time.time() - t0 < 900:
    if log.exists() and re.search(r"time: compiled|Connected to Build server", log.read_text(errors="replace")): break
    time.sleep(2)
print(f"build ready after {time.time() - t0:.0f}s; settling 20s", flush=True); time.sleep(20)
results = []
for k, step in enumerate(seq):
    f = step["file"]; uri = (src / f).as_uri()
    if f not in texts: open_file(f); time.sleep(gap)
    texts[f][step["edit_line"]] += " "; versions[f] += 1
    send("textDocument/didChange", {"textDocument": {"uri": uri, "version": versions[f]}, "contentChanges": [{"text": "\n".join(texts[f])}]}, False)
    time.sleep(gap)
    tp = {"textDocument": {"uri": uri}, "position": {"line": step["line"], "character": step["col"]}}
    ts = time.perf_counter(); r = wait(send("textDocument/hover", tp))
    results.append({"k": k, "file": f, "ms": (r[0] - ts) * 1000 if r else None, "ok": bool(r and r[1].get("result"))})
json.dump(results, open(out, "w"))
print(f"{len(results)} hovers after edits; written {out}", flush=True)
try: wait(send("shutdown", None), 30); send("exit", None, False)
except Exception: pass
time.sleep(2); p.kill()
