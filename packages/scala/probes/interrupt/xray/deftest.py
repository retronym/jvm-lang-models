import json, urllib.request, urllib.parse
def get(path): return json.load(urllib.request.urlopen('http://127.0.0.1:8791' + path))
def req(file, kind, code, offset):
    data = urllib.parse.urlencode({'kind': kind, 'code': code, 'offset': offset, 'cancelAfterMs': -1, 'file': file}).encode()
    return json.load(urllib.request.urlopen(urllib.request.Request('http://127.0.0.1:8791/request', data=data)))
def defn(file, needle, after):
    code = get('/source?file=' + urllib.parse.quote(file))['source']; off = code.index(needle) + len(after)
    r = req(file, 'definition', code, off); h = r.get('hover') or {}
    print(f"  {file or 'A.scala'} {after!r}: {r['outcome']} {r.get('ms')} ms -> found={h.get('found')} {h.get('symbol')} file={h.get('file')} [{h.get('start')},{h.get('end')}) {h.get('how') or h.get('reason')}")
    if h.get('found'):
        tgt = get('/source?file=' + urllib.parse.quote(h['file']))['source'] if h['file'] else code
        print("      ->", tgt[h['start']:h['start'] + 70].replace('\n', ' '))
defn('typer/QuotesAndSplices.scala', 'inferImplicitArg(defn.QuotesClass', 'inferImplicitArg')
defn('typer/QuotesAndSplices.scala', 'inferImplicitArg(defn.QuotesClass', 'inferImplicitArg(defn')
defn('typer/QuotesAndSplices.scala', 'inferImplicitArg(defn.QuotesClass', 'inferImplicitArg(defn.QuotesClass')
defn('typer/Typer.scala', 'ctx.isJava then', 'ctx.isJava')
defn('typer/Typer.scala', 'def typedSelect(', 'def typedSelect')
defn('', 'val r = this.meth', 'val r = this.meth')
defn('', 'xs.map(_ + 3)', 'xs.map')
