#!/usr/bin/env python3
"""Order sensitivity: compile each multi-file program in `order/` jointly in its file order,
jointly reversed, and, after a joint build in order, each file again alone against the joint build's
classfiles (what an incremental build does after an edit to that file).

    order.py [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

A program's files are sections of `order/<name>.scala` headed `// file: <Name>.scala`; a first line
`// only: 3` restricts it to one compiler. Verdicts are
`ok`, `cycle` or `error` (any other error, such as an ambiguous implicit). A program accepted in some modes
and rejected in others is order-sensitive: whether it compiles depends on the order the compiler
forced its facts in, which a well-founded program's never does (`Query.Lazy.forceAll_ok`); one
rejected in every mode with different diagnostics is marked too.
"""
import importlib.util, os, re, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(LEAN, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)
CYCLIC = re.compile(r'cyclic|recursive (method|value) .* needs|Cyclic Error|Overloaded or recursive', re.I)


def verdict(r):
    if r['ok']:
        return 'ok', ''
    msgs = ' | '.join(d['message'].split('\n')[0] for d in compiler.errors(r)) + r.get('crash', '')[:100]
    return ('cycle' if CYCLIC.search(msgs) else 'error'), msgs[:110]


def only(path):
    m = re.search(r'^// only: (\S+)', open(path).read(), re.M)
    return m.group(1) if m else None


def split(path):
    parts = re.split(r'^// file: (\S+)\n', open(path).read(), flags=re.M)
    return [(parts[i], parts[i + 1]) for i in range(1, len(parts), 2)]


def main():
    args = sys.argv[1:]
    versions = [('2.12', '2.12.21'), ('2.13', '2.13.18'), ('3', '3.9.0')]
    for i, a in enumerate(args):
        if a == '--scala212': versions[0] = ('2.12', args[i + 1])
        if a == '--scala2': versions[1] = ('2.13', args[i + 1])
        if a == '--scala3': versions[2] = ('3', args[i + 1])
    progs = sorted(f[:-6] for f in os.listdir(os.path.join(HERE, 'order')) if f.endswith('.scala'))
    work = tempfile.mkdtemp(prefix='order')
    rows = {}
    for tag, v in versions:
        with compiler.scala(v, work=os.path.join(work, f'server-{tag}')) as s:
            for k, p in enumerate(progs):
                if only(os.path.join(HERE, 'order', p + '.scala')) not in (None, tag):
                    continue
                files = split(os.path.join(HERE, 'order', p + '.scala'))
                d = os.path.join(work, tag, str(k)); os.makedirs(d)
                paths = []
                for name, src in files:
                    f = os.path.join(d, name); open(f, 'w').write(f'package o{k}\n' + src); paths.append(f)
                res = {}
                res['in order'] = verdict(s.compile(files=paths, out=os.path.join(d, 'fwd'), id=f'{tag}-{k}-fwd'))
                if len(paths) > 1:
                    res['reversed'] = verdict(s.compile(files=list(reversed(paths)), out=os.path.join(d, 'rev'), id=f'{tag}-{k}-rev'))
                    if res['in order'][0] == 'ok':
                        for j, (name, _) in enumerate(files):
                            r = s.compile(files=[paths[j]], out=os.path.join(d, f'sep{j}'), id=f'{tag}-{k}-sep{j}',
                                          classpath=[f'{tag}-{k}-fwd'])
                            res[f'{name} alone'] = verdict(r)
                rows[(p, tag)] = res
    sensitive = 0
    for p in progs:
        print(f'== {p}')
        for tag, v in versions:
            if (p, tag) not in rows:
                continue
            res = rows[(p, tag)]
            kinds = {r[0] for r in res.values()}
            # accepted in some modes, rejected in others; or rejected everywhere, but differently
            accepts = 'ok' in kinds and len(kinds) > 1
            mark = '   <-- compiles or not by order' if accepts else ('   (diagnostic differs)' if len(kinds) > 1 else '')
            sensitive += accepts
            print(f'  {v:8} ' + ', '.join(f'{m}: {r[0]}' for m, r in res.items()) + mark)
            for m, r in res.items():
                if r[0] != 'ok':
                    print(f'           {m}: {r[1]}')
    print(f'{len(progs)} programs, {len(versions)} compilers: {sensitive} (program, compiler) pairs that compile or not by order')


if __name__ == '__main__':
    main()
