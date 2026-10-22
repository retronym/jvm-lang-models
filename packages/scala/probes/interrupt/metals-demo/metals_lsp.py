"""Drive Metals over stdio on a project: initialize, open a file, send a few
requests (completion, hover, definition, signatureHelp), then read
.metals/metals.log for the [dotc-session] lines of the presentation compiler.
usage: python3 -I metals_lsp.py <metals-launch-cmd...> -- <project-dir> <file> <line>:<col> ..."""
import json, os, subprocess, sys, threading, time, pathlib, re

args = sys.argv[1:]; sep = args.index('--'); cmd, rest = args[:sep], args[sep + 1:]
proj = pathlib.Path(rest[0]).resolve(); rel = rest[1]; positions = rest[2:]
uri = proj.joinpath(rel).as_uri(); text = proj.joinpath(rel).read_text()
log = proj / ".metals" / "metals.log"
p = subprocess.Popen(cmd, cwd=proj, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=open(str(proj / "metals-stderr.log"), "wb"))
seq = 0; pending = {}; notes = []
def send(method, params, is_request=True):
    global seq
    msg = {"jsonrpc": "2.0", "method": method, "params": params}
    if is_request: seq += 1; msg["id"] = seq
    data = json.dumps(msg).encode(); p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data); p.stdin.flush()
    return seq if is_request else None
def reader():
    while True:
        line = p.stdout.readline()
        if not line: return
        if line.lower().startswith(b"content-length:"):
            n = int(line.split(b":")[1]); p.stdout.readline(); body = json.loads(p.stdout.read(n))
            if "id" in body and "method" not in body: pending[body["id"]] = body
            elif "method" in body:
                notes.append(body)
                if "id" in body:  # a server request: answer minimally
                    m = body["method"]; result = None
                    if m == "window/showMessageRequest": result = None
                    elif m == "workspace/configuration": result = [{} for _ in body["params"]["items"]]
                    elif m == "client/registerCapability": result = None
                    data = json.dumps({"jsonrpc": "2.0", "id": body["id"], "result": result}).encode()
                    p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data); p.stdin.flush()
threading.Thread(target=reader, daemon=True).start()
def wait(i, timeout=600):
    t0 = time.time()
    while i not in pending:
        if time.time() - t0 > timeout: return {"error": "timeout"}
        if p.poll() is not None: return {"error": f"metals exited {p.returncode}"}
        time.sleep(0.2)
    return pending.pop(i)
r = wait(send("initialize", {"processId": os.getpid(), "rootUri": proj.as_uri(), "capabilities": {"textDocument": {"completion": {"completionItem": {"snippetSupport": True}}}}, "initializationOptions": {"statusBarProvider": "off", "isExitOnShutdown": True, "icons": "unicode"}}), 120)
print("initialize:", "ok" if "result" in r else r, flush=True)
send("initialized", {}, False)
send("textDocument/didOpen", {"textDocument": {"uri": uri, "languageId": "scala", "version": 1, "text": text}}, False)
# wait for the build import: Metals logs "Imported build" / compiles; poll the log
t0 = time.time(); imported = False
while time.time() - t0 < 900:
    if log.exists() and re.search(r"[Ii]mported build|Compiled root|BSP connection|compiled", log.read_text()): imported = True; break
    if p.poll() is not None: break
    time.sleep(3)
print("build import:", "seen" if imported else "not seen in the log", f"after {time.time() - t0:.0f}s", flush=True)
time.sleep(10)
lines = text.split("\n")
for pos in positions:
    ln, col = [int(x) for x in pos.split(":")]
    tp = {"textDocument": {"uri": uri}, "position": {"line": ln - 1, "character": col - 1}}
    for method in ("textDocument/completion", "textDocument/hover", "textDocument/definition", "textDocument/signatureHelp"):
        t1 = time.time(); r = wait(send(method, tp), 120)
        res = r.get("result"); size = len(res.get("items", res) if isinstance(res, dict) else (res or [])) if res is not None else 0
        print(f"{method:32} {pos:>8} {time.time() - t1:6.2f}s -> {'error ' + str(r['error']) if 'error' in r else f'{type(res).__name__} {size}'}", flush=True)
time.sleep(3)
if log.exists():
    ls = [l for l in log.read_text().split("\n") if "dotc-session" in l]
    print(f"[dotc-session] lines in metals.log: {len(ls)}"); print("\n".join(ls[-12:]))
else: print("no metals.log")
try: wait(send("shutdown", None), 30); send("exit", None, False)
except Exception: pass
time.sleep(2); p.kill()
