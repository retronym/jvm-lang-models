#!/usr/bin/env python3
"""Compile the cycle battery with scalac 2.12 and 2.13 and dotc 3, and check each program's verdicts.

    battery.py [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Each `battery/*.scala` says, in its header, `// expect: <2.12> <2.13> <3>` (`ok` or `cycle`) and
`// kind: ok | true | spurious`: true when no bundling of the program's facts avoids the cycle,
spurious when the program is well-founded and one compiler's bundling cycles where another's does
not. A program is compiled in a package of its own, as the compile server keeps its symbol table
between runs. Prints a table and exits non-zero if any verdict differs.
"""
import importlib.util, os, re, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(LEAN, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)

CYCLIC = re.compile(r'cyclic|recursive (method|value) .* needs|Cyclic Error|TypeError', re.I)


def verdict(r):
    if r['ok']:
        return 'ok'
    msgs = ' '.join(d['message'] for d in compiler.errors(r)) + r.get('crash', '')
    return 'cycle' if CYCLIC.search(msgs) else 'error: ' + msgs[:80]


def main():
    args = sys.argv[1:]
    versions = [('2.12', '2.12.21'), ('2.13', '2.13.18'), ('3', '3.9.0')]
    for i, a in enumerate(args):
        if a == '--scala212': versions[0] = ('2.12', args[i + 1])
        if a == '--scala2': versions[1] = ('2.13', args[i + 1])
        if a == '--scala3': versions[2] = ('3', args[i + 1])
    progs = sorted(f[:-6] for f in os.listdir(os.path.join(HERE, 'battery')) if f.endswith('.scala'))
    work = tempfile.mkdtemp(prefix='battery')
    got, meta = {}, {}
    for j, (tag, v) in enumerate(versions):
        with compiler.scala(v, work=os.path.join(work, f'server-{tag}')) as s:
            for k, p in enumerate(progs):
                src = open(os.path.join(HERE, 'battery', p + '.scala')).read()
                exp = re.search(r'// expect: (.*)', src).group(1).split()
                meta[p] = (exp, re.search(r'// kind: (\w+)', src).group(1))
                f = os.path.join(work, f'{tag}-{k}.scala')
                open(f, 'w').write(f'package b{k}\n' + src)
                got[(p, j)] = verdict(s.compile(files=[f], out=os.path.join(work, f'out-{tag}-{k}'), id=f'{tag}-{k}'))
    bad = 0
    print(f"{'program':32} {'kind':9} " + ' '.join(f'{t:6}' for t, _ in versions))
    for p in progs:
        exp, kind = meta[p]
        cells = []
        for j in range(len(versions)):
            g = got[(p, j)]
            ok = g == exp[j]
            bad += not ok
            cells.append(f'{g:6}' if ok else f'{g} (expected {exp[j]})')
        print(f'{p:32} {kind:9} ' + ' '.join(cells))
    print(f"{len(progs)} programs, {len(versions)} compilers ({', '.join(v for _, v in versions)}): "
          f"{'all verdicts as expected' if not bad else f'{bad} verdicts differ'}")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
