#!/usr/bin/env python3
"""Calibrate packages/scala/Scala/Names.lean (binary names of classes and objects) against scalac and dotc.

    names.py OUT [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Runs `lake exe namesprobe OUT` (from packages/harness), compiles each program OUT/src/pN/*.scala in its own run
with each compiler in a compile server (packages/harness/scripts/compiler.py), and compares, per program, the set
of classfiles: binary name, and the class's own InnerClasses entry (outer class, simple name). Writes
OUT/report-<tag>.txt with every divergence grouped by shape, and prints the agreement counts per family.
"""
import importlib.util, os, subprocess, sys, unicodedata
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('probe', os.path.join(HERE, 'probe.py'))
probe = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe)
compiler = probe.compiler

nfc = lambda s: unicodedata.normalize('NFC', s)


def compile_prog(server, src, dest, pid):
    files = sorted(os.path.join(src, f) for f in os.listdir(src) if f.endswith('.scala'))
    r = server.compile(files=files, out=os.path.join(dest, pid), id=pid)
    if not r['ok']:
        for d in compiler.errors(r)[:2]:
            sys.stderr.write(f"{d['file']}:{d['line']}:{d['column']}: error: {d['message']}\n")
        sys.stderr.write(r.get('crash', '')[:300])
        return None
    return r['out']


def classfiles(out):
    """{(binary name, outer, simple)} for the classfiles under `out`."""
    got = set()
    for root, _, fs in os.walk(out):
        for f in fs:
            if not f.endswith('.class'):
                continue
            c = probe.read_class(os.path.join(root, f))
            own = [e for e in c['inner'] if e[0] == c['name']]
            o, s = (own[0][1] or '-', own[0][2] or '-') if own else ('-', '-')
            got.add((nfc(c['name']), nfc(o), nfc(s)))
    return got


def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0] if args else 'out-names')
    versions = {'2.12': '2.12.21', '2.13': '2.13.18', '3': '3.9.0'}
    for i, a in enumerate(args):
        if a == '--scala212': versions['2.12'] = args[i + 1]
        if a == '--scala2': versions['2.13'] = args[i + 1]
        if a == '--scala3': versions['3'] = args[i + 1]
    subprocess.run(['lake', 'exe', 'namesprobe', out], cwd=os.path.join(LEAN, 'packages', 'harness'), check=True)
    index = [l.split('\t') for l in open(os.path.join(out, 'index.txt'), encoding='utf-8').read().splitlines() if l]
    fam = {pid: f for pid, f, _, _ in index}
    fresh = {pid for pid, _, _, fr in index if fr == 'fresh'}
    for tag, version in versions.items():
        exp = defaultdict(set)
        for l in open(os.path.join(out, f'expected-{tag}.txt'), encoding='utf-8').read().splitlines():
            pid, b, o, s = l.split('\t')
            exp[pid].add((nfc(b), nfc(o), nfc(s)))
        pids = [pid for pid, _, only3, _ in index if tag == '3' or only3 != '3']
        groups = defaultdict(list)
        bad = set()
        def check(server, n, pid):
            d = compile_prog(server, os.path.join(out, 'src', pid), os.path.join(out, f'classes-{tag}'), pid)
            if any(e[0] == '!unwritable' for e in exp[pid]):
                if d is not None:
                    groups[(fam[pid], 'model: a name too long for a file; it compiled')].append(pid); bad.add(pid)
                return
            if d is None:
                groups[(fam[pid], 'does not compile')].append(pid); bad.add(pid); return
            act = classfiles(d)
            for e in sorted(exp[pid] - act):
                groups[(fam[pid], f'only model: {e[0]} inner {e[1]} {e[2]}')].append(pid); bad.add(pid)
            for a in sorted(act - exp[pid]):
                groups[(fam[pid], f'only {tag}: {a[0]} inner {a[1]} {a[2]}')].append(pid); bad.add(pid)
        with compiler.scala(version, work=os.path.join(out, f'server-{tag}')) as server:
            for n, pid in enumerate(p for p in pids if p not in fresh):
                check(server, n, pid)
                if (n + 1) % 100 == 0:
                    print(f'  {tag}: {n + 1}/{len(pids)} compiled, {len(bad)} diverge', flush=True)
        # a program in the empty package gets a compiler of its own (see NamesProbe)
        for pid in pids:
            if pid in fresh:
                with compiler.scala(version, work=os.path.join(out, f'server-{tag}-{pid}')) as server:
                    check(server, 0, pid)
        famcount, badfam = defaultdict(int), defaultdict(int)
        for pid in pids:
            famcount[fam[pid]] += 1
            badfam[fam[pid]] += pid in bad
        summary = ', '.join(f'{f} {famcount[f] - badfam[f]}/{famcount[f]}' for f in sorted(famcount))
        line = f'{tag} ({version}): {len(pids) - len(bad)}/{len(pids)} programs agree ({summary}); {len(groups)} divergence shapes'
        print(line, flush=True)
        with open(os.path.join(out, f'report-{tag}.txt'), 'w', encoding='utf-8') as rep:
            rep.write(line + '\n\n')
            for (f, d), ps in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                rep.write(f'{len(ps):5d}  {f}\t{d}\te.g. {" ".join(ps[:4])}\n')


if __name__ == '__main__':
    main()
