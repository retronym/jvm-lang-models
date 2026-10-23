"""Replay one hover+definition sequence against Metals over stdio; print per-request round-trip times.
usage: python3 -I replay_lsp.py <metals launch...> -- <project-dir> <sequence.json> <out.json>"""
import json, os, subprocess, sys, threading, time, pathlib, re
args = sys.argv[1:]; sep = args.index('--'); cmd, rest = args[:sep], args[sep + 1:]
proj = pathlib.Path(rest[0]).resolve(); seq = json.load(open(rest[1])); out = rest[2]
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
first = seq[0]["file"]; send("textDocument/didOpen", {"textDocument": {"uri": (src / first).as_uri(), "languageId": "scala", "version": 1, "text": (src / first).read_text()}}, False)
opened = {first}
t0 = time.time()
while time.time() - t0 < 900:
    if log.exists() and "time: compiled" in log.read_text(errors="replace"): break
    time.sleep(2)
print(f"build compiled after {time.time() - t0:.0f}s; settling 15s", flush=True); time.sleep(15)
results = []; prev = None
for k, pos in enumerate(seq):
    f = pos["file"]; uri = (src / f).as_uri()
    if f not in opened:
        send("textDocument/didOpen", {"textDocument": {"uri": uri, "languageId": "scala", "version": 1, "text": (src / f).read_text()}}, False); opened.add(f)
    tp = {"textDocument": {"uri": uri}, "position": {"line": pos["line"], "character": pos["col"]}}
    for method in ("textDocument/hover", "textDocument/definition"):
        ts = time.perf_counter(); r = wait(send(method, tp))
        ms = (r[0] - ts) * 1000 if r else None
        results.append({"k": k, "file": f, "method": method.split("/")[1], "ms": ms, "switch": f != prev, "ok": bool(r and r[1].get("result"))})
    prev = f
json.dump(results, open(out, "w"))
print(f"{len(results)} requests; written {out}", flush=True)
try: wait(send("shutdown", None), 30); send("exit", None, False)
except Exception: pass
time.sleep(2); p.kill()
