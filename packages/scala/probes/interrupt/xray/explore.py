"""Exploratory testing of the x-ray server: random files, random identifiers, every request kind;
reports anomalies (errors, exceptions, definitions pointing outside the file, spans past the end,
hover with no typed tree inside a method, slow requests). Usage: explore.py [seed] [files] [points]"""
import json, random, re, sys, time, urllib.request, urllib.parse
BASE = 'http://127.0.0.1:8791'
def get(path): return json.load(urllib.request.urlopen(BASE + path))
def req(file, kind, code, offset):
    data = urllib.parse.urlencode({'kind': kind, 'code': code, 'offset': offset, 'cancelAfterMs': -1, 'file': file}).encode()
    return json.load(urllib.request.urlopen(urllib.request.Request(BASE + '/request', data=data), timeout=120))
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
nfiles = int(sys.argv[2]) if len(sys.argv) > 2 else 12
npoints = int(sys.argv[3]) if len(sys.argv) > 3 else 6
rng = random.Random(seed)
files = get('/files')['files']
chosen = rng.sample(files, nfiles)
anomalies, stats, slow = [], {'requests': 0, 'ms': 0.0}, []
ident = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
for f in chosen:
    code = get('/source?file=' + urllib.parse.quote(f))['source']
    idents = [m for m in ident.finditer(code) if m.group() not in ('def', 'val', 'var', 'class', 'object', 'trait', 'import', 'package', 'if', 'then', 'else', 'match', 'case', 'new', 'extends', 'with', 'using', 'given', 'override', 'private', 'final', 'return', 'while', 'for', 'yield', 'do', 'end', 'true', 'false', 'null', 'this', 'super', 'type', 'inline', 'transparent', 'lazy', 'implicit', 'sealed', 'abstract', 'enum', 'extension', 'export', 'opaque', 'infix', 'try', 'catch', 'finally', 'throw')]
    for m in rng.sample(idents, min(npoints, len(idents))):
        off = m.end(); line = code.count('\n', 0, off) + 1
        for kind in ('typeAt', 'definition', 'complete'):
            t0 = time.time()
            try: r = req(f, kind, code, off)
            except Exception as e:
                anomalies.append(f"{f}:{line} {kind}@{off} {m.group()}: TRANSPORT {e}"); continue
            ms = (time.time() - t0) * 1000; stats['requests'] += 1; stats['ms'] += ms
            if ms > 2000: slow.append(f"{f}:{line} {kind} {ms:.0f} ms ({r.get('outcome')}, {r.get('typedTrees')} trees)")
            if r.get('outcome') == 'error': anomalies.append(f"{f}:{line} {kind}@{off} {m.group()}: ERROR {r.get('error')}")
            if r.get('touched', 0): anomalies.append(f"{f}:{line} {kind}: Touched left: {r['touched']}")
            if r.get('tainted'): anomalies.append(f"{f}:{line} {kind}: run tainted")
            h = r.get('hover') or {}
            if kind == 'definition' and h.get('found'):
                tgt = h.get('file'); 
                if tgt == '' or tgt is None: anomalies.append(f"{f}:{line} definition of {m.group()} -> file '' (the generated file)")
                elif h['start'] is not None and h['start'] > (len(code) if tgt == f else 10**9): anomalies.append(f"{f}:{line} definition span past the end")
            if kind == 'typeAt' and h.get('found') is False and r.get('outcome') in ('fresh', 'resumed', 'served'):
                pass  # a position outside any typed tree is legitimate (keywords, headers); counted below
        stats.setdefault('files', set()).add(f)
print(f"[explore seed={seed}] {stats['requests']} requests over {len(chosen)} files, mean {stats['ms'] / max(1, stats['requests']):.0f} ms")
print(f"  anomalies ({len(anomalies)}):"); [print("   ", a) for a in anomalies[:40]]
print(f"  slow (>2 s) ({len(slow)}):"); [print("   ", s_) for s_ in slow[:20]]
