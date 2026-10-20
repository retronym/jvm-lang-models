#!/usr/bin/env python3
"""Order sensitivity, after scala/scala's `DeterminismTester` (test/junit/scala/tools/nsc), with
accept-or-reject verdicts and separate compilation added.

    order.py [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Per program and compiler:

* the *reference*: all files jointly, in the program's file order (or, if that is rejected, the
  first order that compiles);
* every permutation of every nonempty subset of the files (`DeterminismTester.permutationsWithSubsets`):
  the whole set jointly from scratch in that order, a proper subset from source in that order with
  the rest read as the reference's classfiles (what an incremental build does after an edit to it);
* `separate a→b→…`: every permutation, one file at a time from scratch, each against the
  classfiles of those before it (separate compilation, as across subprojects).

A program's files are sections of `order/<name>.scala` headed `// file: <Name>.scala`; a first line
`// only: 3` restricts it to one compiler. Verdicts: `same` (compiles, and every classfile and TASTy
file it writes is byte-identical to the reference's, as `DeterminismTester.assertDirectorySame`
requires), `members` (compiles, and a classfile's members differ: flags, superclass, interfaces,
fields or methods), `tasty` (compiles, and only TASTy or classfile attributes differ, such as the
TASTy UUID: the pickling artefact of scala/scala3#26551), `cycle`, `error` (any other error, such as an
ambiguous implicit) or `n/a` (a file needs one not yet compiled: "not found"). A program accepted
in some modes and rejected in others compiles or not by order; one that always compiles but with
different members is nondeterministic where it matters to linking. A well-founded program is neither (`Query.Lazy.forceAll_ok`).
"""
import importlib.util, itertools, os, re, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(LEAN, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)
_pspec = importlib.util.spec_from_file_location('probe', os.path.join(HERE, '..', 'probe.py'))
probe = importlib.util.module_from_spec(_pspec)
_pspec.loader.exec_module(probe)
CYCLIC = re.compile(r'cyclic|recursive (method|value) .* needs|Cyclic Error|Overloaded or recursive', re.I)
MISSING = re.compile(r'not found|Not Found Error|is not a member of package', re.I)


def verdict(r):
    if r['ok']:
        return 'ok', ''
    msgs = ' | '.join(d['message'].split('\n')[0] for d in compiler.errors(r)) + r.get('crash', '')[:100]
    if CYCLIC.search(msgs):
        return 'cycle', msgs[:110]
    return ('n/a' if MISSING.search(msgs) else 'error'), msgs[:110]


def outputs(d):
    """{relative path: bytes} of the classfiles and TASTy files under `d`."""
    out = {}
    for root, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(('.class', '.tasty')):
                p = os.path.join(root, f)
                out[os.path.relpath(p, d)] = open(p, 'rb').read()
    return out


def shape(data):
    """A classfile's members, as linking and javac see them: flags, superclass, interfaces, fields
    and methods with their access and descriptors (no attributes, so no TASTy UUID, no bodies)."""
    f = tempfile.NamedTemporaryFile(suffix='.class', delete=False)
    f.write(data); f.close()
    try:
        c = probe.read_class(f.name)
    finally:
        os.unlink(f.name)
    return (c['acc'], c['name'], c['sup'], tuple(c['ifaces']),
            tuple(sorted((a, n, d) for a, n, d, _ in c['fields'])),
            tuple(sorted((a, n, d) for a, n, d, _ in c['methods'])))


def against(ref, got, whole):
    """`same` if every file written is byte-identical to the reference's (and, for the whole set,
    no file is missing or extra); `members` if a classfile's members differ, or a file is missing or
    extra; else `tasty`: only TASTy files or classfile attributes (such as the TASTy UUID) differ."""
    diff = sorted(f for f in got if ref.get(f) != got[f])
    missing = sorted(set(ref) - set(got)) if whole else []
    if not diff and not missing:
        return 'same', ''
    semantic = missing + [f for f in diff if f.endswith('.class') and (f not in ref or shape(ref[f]) != shape(got[f]))]
    if semantic:
        return 'members', ', '.join(semantic[:3])
    return 'tasty', ', '.join(diff[:3])


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
                names = [n for n, _ in files]
                n = len(paths)

                def compile_(srcs, cp, key):
                    return s.compile(files=srcs, out=os.path.join(d, key), id=f'{tag}-{k}-{key}', classpath=cp)

                # the reference: the file order, or the first order that compiles
                ref = None
                for perm in [tuple(range(n))] + [q for q in itertools.permutations(range(n)) if q != tuple(range(n))]:
                    key = 'j' + ''.join(map(str, perm))
                    r = compile_([paths[x] for x in perm], [], key)
                    v = verdict(r)
                    mode = 'joint ' + ', '.join(names[x] for x in perm)
                    if v[0] == 'ok' and ref is None:
                        ref, refkey = outputs(r['out']), key
                        res[mode + ' (reference)'] = ('same', '')
                    elif v[0] == 'ok':
                        res[mode] = against(ref, outputs(r['out']), True)
                    else:
                        res[mode] = v
                # a proper subset from source, in every order, the rest from the reference's classfiles
                if ref is not None and n > 1:
                    seen = set()
                    for perm in itertools.permutations(range(n)):
                        for size in range(n - 1, 0, -1):
                            sub = perm[:size]
                            if sub in seen:
                                continue
                            seen.add(sub)
                            key = 's' + ''.join(map(str, sub))
                            r = compile_([paths[x] for x in sub], [f'{tag}-{k}-{refkey}'], key)
                            v = verdict(r)
                            mode = ', '.join(names[x] for x in sub) + ' from source'
                            res[mode] = against(ref, outputs(r['out']), False) if v[0] == 'ok' else v
                # separate compilation from scratch, one file at a time, in every order
                if n > 1:
                    for perm in itertools.permutations(range(n)):
                        cp, outcome, got = [], ('ok', ''), {}
                        for step, x in enumerate(perm):
                            key = 'c' + ''.join(map(str, perm)) + f'-{step}'
                            r = compile_([paths[x]], cp, key)
                            outcome = verdict(r)
                            if outcome[0] != 'ok':
                                break
                            got.update(outputs(r['out']))
                            cp = cp + [f'{tag}-{k}-{key}']
                        if outcome[0] == 'ok' and ref is not None:
                            outcome = against(ref, got, True)
                        res['separate ' + '→'.join(names[x] for x in perm)] = outcome
                rows[(p, tag)] = res
    sensitive = 0
    for p in progs:
        print(f'== {p}')
        for tag, v in versions:
            if (p, tag) not in rows:
                continue
            res = rows[(p, tag)]
            kinds = {r[0] for r in res.values()} - {'n/a'}
            compiles = kinds & {'same', 'tasty', 'members'}
            fails = kinds & {'cycle', 'error'}
            # accepted in some modes, rejected in others; compiled to different bytes; or rejected
            # everywhere, but differently
            if compiles and fails:
                mark = '   <-- compiles or not by order'
            elif 'members' in kinds:
                mark = '   <-- classfile members depend on order'
            elif len(fails) > 1:
                mark = '   (diagnostic differs)'
            else:
                mark = ''
            sensitive += bool(compiles and fails) or 'members' in kinds
            print(f'  {v:8}{mark}')
            for m, r in res.items():
                print(f'           {m}: {r[0]}' + (f'  ({r[1]})' if r[0] not in ('same', 'n/a') else ''))
    print(f'{len(progs)} programs, {len(versions)} compilers: {sensitive} (program, compiler) pairs that compile or not, or compile differently, by order')


if __name__ == '__main__':
    main()
