import json, urllib.request, urllib.parse, sys
def get(path): return json.load(urllib.request.urlopen('http://127.0.0.1:8791' + path))
def req(file, kind, code, offset):
    data = urllib.parse.urlencode({'kind': kind, 'code': code, 'offset': offset, 'cancelAfterMs': -1, 'file': file}).encode()
    return json.load(urllib.request.urlopen(urllib.request.Request('http://127.0.0.1:8791/request', data=data)))
src = {}
def code(file, edit=False):
    if file not in src: src[file] = get('/source?file=' + urllib.parse.quote(file))['source']
    return ('// edit\n' + src[file]) if edit else src[file]
def typeat(file, needle, after, edit=False):
    c = code(file, edit); off = c.index(needle) + len(after)
    r = req(file, 'typeAt', c, off); h = r.get('hover') or {}
    print(f"  {file}{' (edited)' if edit else ''} {after!r}: {r['outcome']} run {r.get('runId')} {r.get('typedTrees')} trees {r.get('ms')} ms diags={r.get('diagnostics')} -> {h.get('symbol') or h.get('tree')} | {str(h.get('type'))[:60]}")
    for d in r.get('diagnosticText') or []:
        if 'Implicit conversion' not in d and 'warning' not in d: print("      diag", d[:200])
    return h
Q = ('typer/QuotesAndSplices.scala', 'inferImplicitArg(defn.QuotesClass', 'inferImplicitArg')
steps = sys.argv[1:]
for s in steps:
    if s == 'q': typeat(*Q)
    if s == 't': typeat('typer/Typer.scala', 'ctx.isJava then', 'ctx.isJava')
    if s == 'te': typeat('typer/Typer.scala', 'ctx.isJava then', 'ctx.isJava', edit=True)
    if s == 'a': typeat('typer/Applications.scala', 'def spliceMeth', 'def spliceMeth')
    if s == 'c': typeat('typer/ConstFold.scala', 'def foldSubrangeOp', 'def foldSubrangeOp')
