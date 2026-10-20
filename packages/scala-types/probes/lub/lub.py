#!/usr/bin/env python3
"""Track LUB: the inferred type of a join, and its algebraic laws, on scalac 2.12, 2.13 and dotc 3.

    python3 -I lub.py [--only WORLD,...] [--scala212 V] [--scala2 V] [--scala3 V] [--out FILE]

A *world* (`worlds.py`) is a small hierarchy and a few values. For each world the probe writes a client object
whose `val`s join the values in every shape it checks:

* `if (c) x else y` for every ordered pair (commutativity: `x,y` against `y,x`), and `List(x, y)`;
* `List(x, y, z)` for every permutation of every triple, and `c match { case 0 => x; case 1 => y; case _ => z }`;
* `lub(lub(x, y), z)` and `lub(x, lub(y, z))`, the inner join a `val` of its own so its type is inferred,
  widened (dotc) and fixed before the outer join sees it (associativity);
* `lub(lub(x, y), x)` (absorption: joining a type already below the join changes nothing).

Each world is compiled twice per compiler: *joint* (hierarchy and client in one run) and *separate* (the
hierarchy first; the client in a fresh run against its classfiles, as an incremental build sees it).

The inferred type is read from the compiler's own printing of the typed tree (`-Xprint:typer`, `-Vprint:typer`):
the `val`'s type tree after typer is the type the namer assigned, before erasure or any later phase rewrites it,
printed by the compiler that computed it. The alternatives are worse: an error message (`found: T`) shortens and
simplifies; a Java generic signature has already erased refinements, and the order of a compound type's parents
survives only in its first element; reflection on the pickle or TASTy needs scala-reflect or a TASTy inspector
per compiler. We also read the accessor's erased descriptor and generic `Signature` from the classfile, because
that is where a difference in parent order becomes a difference in linking.
"""
import importlib.util, itertools, json, os, re, struct, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(LEAN, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)
_wspec = importlib.util.spec_from_file_location('worlds', os.path.join(HERE, 'worlds.py'))
worlds = importlib.util.module_from_spec(_wspec)
_wspec.loader.exec_module(worlds)


# ---- the client program -------------------------------------------------------------------------------------

def cases(world):
    """[(val name, right-hand side, law tags)]: the joins to infer, named so the laws can find their partners."""
    vals = world['values']
    names = list(vals)
    out = []
    for x, y in itertools.permutations(names, 2):
        out.append((f'if_{x}_{y}', f'if (c) {vals[x]} else {vals[y]}'))
        out.append((f'list2_{x}_{y}', f'List({vals[x]}, {vals[y]})'))
    for t in itertools.combinations(names[:world.get('triples_of', 4)], 3):
        for x, y, z in itertools.permutations(t):
            out.append((f'list3_{x}_{y}_{z}', f'List({vals[x]}, {vals[y]}, {vals[z]})'))
            out.append((f'match_{x}_{y}_{z}', f'(n match {{ case 0 => {vals[x]}; case 1 => {vals[y]}; case _ => {vals[z]} }})'))
            # (x ⊔ y) ⊔ z, the inner join fixed in a val; x ⊔ (y ⊔ z) is (y ⊔ z) ⊔ x, written as its own permutation
            out.append((f'assoc_{x}_{y}_{z}', f'if (c) if_{x}_{y} else {vals[z]}'))
    for x, y in itertools.permutations(names, 2):
        out.append((f'absorb_{x}_{y}', f'if (c) if_{x}_{y} else {vals[x]}'))
    return out


def sources(world, pkg):
    """(hierarchy source, client source) for package `pkg`."""
    hier = f'package {pkg}\n\n{world["decls"].strip()}\n'
    body = '\n'.join(f'  val {n} = {rhs}' for n, rhs in cases(world))
    client = f'package {pkg}\n\nobject Client {{\n  def c: Boolean = true\n  def n: Int = 0\n{body}\n}}\n'
    return hier, client


# ---- reading the typed tree ---------------------------------------------------------------------------------

def val_types(printed, names):
    """{val name: its type as printed after typer}. A type is read from after `val name: ` to the ` =` at
    bracket depth 0, newlines and indentation collapsed (dotc breaks long types over lines)."""
    out = {}
    for n in names:
        m = re.search(r'\bval ' + re.escape(n) + r':\s+', printed)
        if not m:
            continue
        i, depth, buf = m.end(), 0, []
        while i < len(printed):
            ch = printed[i]
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif depth == 0 and printed.startswith(' =', i) and not printed.startswith(' =>', i):
                break
            elif depth == 0 and printed.startswith(';', i):
                break
            elif depth == 0 and ch == '\n':
                rest = printed[i:].lstrip()
                if rest.startswith('=') and not rest.startswith('=>'):
                    break
            buf.append(ch)
            i += 1
        out[n] = re.sub(r'\s+', ' ', ''.join(buf)).strip()
    return out


def normal(tp, pkg):
    """The printed type without the package prefixes that only add noise."""
    tp = tp.replace(pkg + '.', '').replace('_root_.', '')
    tp = re.sub(r'\bscala\.collection\.immutable\.', '', tp)
    tp = re.sub(r'\bscala\.(?=[A-Z])', '', tp)
    tp = re.sub(r'\bjava\.lang\.(?=[A-Z])', '', tp)
    tp = tp.replace('Client.this.', '').replace('Client.', '')
    return tp


def split_top(tp, seps):
    """`tp` split at bracket depth 0 on any of `seps`."""
    parts, depth, cur, i = [], 0, '', 0
    while i < len(tp):
        ch = tp[i]
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        sep = next((x for x in seps if depth == 0 and tp.startswith(x, i)), None)
        if sep:
            parts.append(cur.strip()); cur = ''; i += len(sep); continue
        cur += ch
        i += 1
    parts.append(cur.strip())
    return parts


def top_parents(tp):
    """The parents of a compound type at bracket depth 0 (`A with B { refinement }` or `A & B`), in order."""
    return split_top(tp, (' with ', ' & '))


def canon(tp):
    """`tp` with the operands of every union and intersection sorted, at every depth: equal canonical forms
    mean the types differ at most in the order of `|`, `&` and `with` operands."""
    w = re.match(r'^([?_]) (>:|<:) (.*)$', tp)
    if w:
        if w.group(2) == '>:':
            parts = split_top(w.group(3), (' <: ',))
            lo, hi = parts[0], (parts[1] if len(parts) > 1 else '')
        else:
            lo, hi = '', w.group(3)
        return w.group(1) + (f' >: {canon(lo)}' if lo else '') + (f' <: {canon(hi)}' if hi else '')
    ors = split_top(tp, (' | ',))
    if len(ors) > 1:
        return ' | '.join(sorted(canon(t) for t in ors))
    ands = split_top(tp, (' with ', ' & '))
    if len(ands) > 1:
        return ' & '.join(sorted(canon(t) for t in ands))
    m = re.match(r'^([^\[]+)\[(.*)\]$', tp)
    if m:
        return m.group(1) + '[' + ', '.join(canon(a) for a in split_top(m.group(2), (', ',))) + ']'
    if tp.startswith('(') and tp.endswith(')'):
        return canon(tp[1:-1])
    return tp


def same_up_to_order(a, b):
    return canon(a) == canon(b)


# ---- reading the classfile ----------------------------------------------------------------------------------

def methods_with_signature(path):
    """{method name: (descriptor, generic Signature or None)}."""
    b = open(path, 'rb').read()
    n, = struct.unpack('>H', b[8:10])
    cp, pos, i = [None] * n, 10, 1
    while i < n:
        tag = b[pos]
        if tag == 1:
            ln, = struct.unpack('>H', b[pos + 1:pos + 3]); cp[i] = b[pos + 3:pos + 3 + ln].decode('utf-8', 'replace'); pos += 3 + ln
        elif tag in (3, 4): pos += 5
        elif tag in (5, 6): pos += 9; i += 1
        elif tag in (7, 8, 16, 19, 20): pos += 3
        elif tag in (9, 10, 11, 12, 17, 18): pos += 5
        elif tag == 15: pos += 4
        else: raise ValueError(f'{path}: tag {tag}')
        i += 1
    pos += 6
    ni, = struct.unpack('>H', b[pos:pos + 2]); pos += 2 + 2 * ni

    def members():
        nonlocal pos
        cnt, = struct.unpack('>H', b[pos:pos + 2]); pos += 2
        out = {}
        for _ in range(cnt):
            a, nn, dd, na = struct.unpack('>HHHH', b[pos:pos + 8]); pos += 8
            sig = None
            for _ in range(na):
                an, al = struct.unpack('>HI', b[pos:pos + 6])
                if cp[an] == 'Signature':
                    sig = cp[struct.unpack('>H', b[pos + 6:pos + 8])[0]]
                pos += 6 + al
            out[cp[nn]] = (cp[dd], sig)
        return out
    members()
    return members()


# ---- running ------------------------------------------------------------------------------------------------

def compile_world(server, tag, wname, world, mode, work):
    pkg = f'lub_{wname}_{mode}'.replace('-', '_')
    hier, client = sources(world, pkg)
    d = os.path.join(work, tag, pkg)
    os.makedirs(d, exist_ok=True)
    printopt = {'2.12': ['-Xprint:typer'], '2.13': ['-Vprint:typer'], '3': ['-Vprint:typer', '-pagewidth', '10000']}[tag]
    opts = printopt + world.get('options', {}).get(tag, [])
    if mode == 'joint':
        r = server.compile(sources={f'{pkg}/Hier.scala': hier, f'{pkg}/Client.scala': client}, options=opts,
                           out=os.path.join(d, 'joint'), id=f'{tag}-{pkg}')
    else:
        h = server.compile(sources={f'{pkg}/Hier.scala': hier}, options=world.get('options', {}).get(tag, []),
                           out=os.path.join(d, 'hier'), id=f'{tag}-{pkg}-h')
        if not h['ok']:
            return h, pkg
        r = server.compile(sources={f'{pkg}/Client.scala': client}, options=opts, classpath=[f'{tag}-{pkg}-h'],
                           out=os.path.join(d, 'client'), id=f'{tag}-{pkg}')
    return r, pkg


def printed(r):
    """The typer printout: on stdout for scalac, as INFO diagnostics for dotc."""
    text = r.get('stdout', '')
    for dg in r.get('diagnostics', []):
        if dg['severity'] == 'INFO' and 'syntax trees at end of' in dg['message']:
            text += dg['message']
    # only the client's tree
    k = text.find('object Client')
    return text[k:] if k >= 0 else text


def probe(versions, only, out):
    names = [w for w in worlds.WORLDS if not only or w in only]
    work = tempfile.mkdtemp(prefix='lub')
    results = {}
    t0 = time.time()
    for tag, ver in versions:
        with compiler.scala(ver, work=os.path.join(work, f'server-{tag}')) as s:
            for wname in names:
                world = worlds.WORLDS[wname]
                if tag in world.get('skip', ()):
                    continue
                for mode in ('joint', 'separate'):
                    r, pkg = compile_world(s, tag, wname, world, mode, work)
                    key = f'{wname}/{tag}/{mode}'
                    if not r['ok']:
                        errs = [e['message'].split('\n')[0] for e in compiler.errors(r)][:3]
                        results[key] = {'error': errs or [r.get('crash', '')[:300]]}
                        print(f'[{time.time() - t0:5.0f}s] {key}: ERROR {errs[:1]}', flush=True)
                        continue
                    vnames = [n for n, _ in cases(world)]
                    types = {n: normal(t, pkg) for n, t in val_types(printed(r), vnames).items()}
                    cls = os.path.join(r['out'], pkg, 'Client$.class')
                    sigs = methods_with_signature(cls) if os.path.exists(cls) else {}
                    erased = {n: [x.replace(pkg + '/', '') if x else x for x in sigs[n]] for n in vnames if n in sigs}
                    results[key] = {'types': types, 'erased': erased,
                                    'missing': [n for n in vnames if n not in types]}
                    sample = next(iter(types.items()), ('-', '-'))
                    print(f'[{time.time() - t0:5.0f}s] {key}: {len(types)} vals; e.g. {sample[0]}: {sample[1]}', flush=True)
    json.dump(results, open(out, 'w'), indent=1, sort_keys=True)
    return results


# ---- the laws -----------------------------------------------------------------------------------------------

def verdict(a, b):
    if a == b:
        return 'same'
    if same_up_to_order(a, b):
        return 'order'
    return 'differs'


def erasure_note(erased, n1, n2):
    if not erased or n1 not in erased or n2 not in erased or erased[n1] == erased[n2]:
        return ''
    return f'  [erasure {erased[n1][1] or erased[n1][0]} vs {erased[n2][1] or erased[n2][0]}]'


def laws(world, types, erased=None):
    """[(law, instance, verdict, detail)] for one world under one compiler and mode."""
    vals = list(world['values'])
    rows = []
    for x, y in itertools.combinations(vals, 2):
        for shape in ('if', 'list2'):
            a, b = types.get(f'{shape}_{x}_{y}'), types.get(f'{shape}_{y}_{x}')
            if a and b:
                rows.append(('comm', f'{shape}({x},{y})', verdict(a, b), f'{a}  |  {b}' + erasure_note(erased, f'{shape}_{x}_{y}', f'{shape}_{y}_{x}')))
    for t in itertools.combinations(vals[:world.get('triples_of', 4)], 3):
        perms = list(itertools.permutations(t))
        for shape in ('list3', 'match', 'assoc'):
            got = {p: types.get(f'{shape}_{"_".join(p)}') for p in perms}
            got = {p: v for p, v in got.items() if v}
            if len(got) < 2:
                continue
            first = next(iter(got.values()))
            vs = [verdict(first, v) for v in got.values()]
            v = 'differs' if 'differs' in vs else 'order' if 'order' in vs else 'same'
            distinct = sorted(set(got.values()))
            rows.append(('perm', f'{shape}({",".join(t)})', v, '  |  '.join(distinct)))
        # associativity: (x ⊔ y) ⊔ z against the flat join List(x, y, z)
        for p in perms:
            a, b = types.get(f'assoc_{"_".join(p)}'), types.get(f'list3_{"_".join(p)}')
            if a and b:
                b = b[5:-1] if b.startswith('List[') else b
                rows.append(('assoc', f'({p[0]}⊔{p[1]})⊔{p[2]} vs List', verdict(a, b), f'{a}  |  {b}'))
    for x, y in itertools.permutations(vals, 2):
        a, b = types.get(f'absorb_{x}_{y}'), types.get(f'if_{x}_{y}')
        if a and b:
            rows.append(('absorb', f'({x}⊔{y})⊔{x}', verdict(a, b), f'{a}  |  {b}'))
    return rows


def report(versions, results, out):
    lines = []
    w = lines.append
    tags = [t for t, _ in versions]
    for wname, world in worlds.WORLDS.items():
        if not any(k.startswith(wname + '/') for k in results):
            continue
        w(f'== {wname}: {world.get("doc", "")}')
        w('   ' + world['decls'].strip().replace('\n', '\n   '))
        w('   values: ' + ', '.join(f'{k} = {v}' for k, v in world['values'].items()))
        # inferred types, one line per val, per compiler and mode
        vnames = [n for n, _ in cases(world) if n.startswith(('if_', 'assoc_'))]
        cut = lambda t, k=160: t if len(t) <= k else t[:k] + '…'
        for n in vnames:
            cells, prev = [], None
            for tag in tags:
                j = results.get(f'{wname}/{tag}/joint', {}).get('types', {}).get(n, '?')
                sp = results.get(f'{wname}/{tag}/separate', {}).get('types', {}).get(n, '?')
                cell = cut(j) + ('' if sp == j else f'  [separate: {cut(sp)}]')
                cells.append(f'{tag}: ' + ('=' if cell == prev else cell))
                prev = cell
            w(f'   {n:22} ' + '   '.join(cells))
        # erasure differences between joint and separate
        for tag in tags:
            j = results.get(f'{wname}/{tag}/joint', {}).get('erased', {})
            sp = results.get(f'{wname}/{tag}/separate', {}).get('erased', {})
            diff = [n for n in sorted(j) if j.get(n) and sp.get(n) and j[n] != sp[n]]
            for n in diff[:3]:
                w(f'   erasure {tag} {n}: joint {j[n][1] or j[n][0]}, separate {sp[n][1] or sp[n][0]}')
            if len(diff) > 3:
                w(f'   erasure {tag}: {len(diff)} of {len(j)} vals erase differently, joint against separate')
        # laws
        for tag in tags:
            for mode in ('joint', 'separate'):
                res = results.get(f'{wname}/{tag}/{mode}')
                if not res:
                    continue
                if 'error' in res:
                    w(f'   {tag} {mode}: ERROR {res["error"]}')
                    continue
                rows = laws(world, res['types'], res.get('erased'))
                bad = [r for r in rows if r[2] != 'same']
                summary = {}
                for law, _, v, _ in rows:
                    summary.setdefault(law, {}).setdefault(v, 0)
                    summary[law][v] += 1
                w(f'   {tag} {mode}: ' + '; '.join(f'{law} ' + ', '.join(f'{v} {c}' for v, c in sorted(vs.items()))
                                           for law, vs in summary.items()))
                shown = {}
                for law, inst, v, detail in bad:
                    shown[law] = shown.get(law, 0) + 1
                    if shown[law] <= 3:
                        w(f'      {law} {inst}: {v}: {cut(detail, 400)}')
        w('')
    text = '\n'.join(lines)
    open(out, 'w').write(text + '\n')
    return text


def main():
    args = sys.argv[1:]
    versions = [('2.12', '2.12.21'), ('2.13', '2.13.18'), ('3', '3.9.0')]
    only, out = None, os.path.join(HERE, 'results.txt')
    for i, a in enumerate(args):
        if a == '--scala212': versions[0] = ('2.12', args[i + 1])
        if a == '--scala2': versions[1] = ('2.13', args[i + 1])
        if a == '--scala3': versions[2] = ('3', args[i + 1])
        if a == '--only': only = set(args[i + 1].split(','))
        if a == '--out': out = args[i + 1]
    results = probe(versions, only, os.path.join(tempfile.gettempdir(), 'lub-results.json'))
    print(report(versions, results, out))


if __name__ == '__main__':
    main()
