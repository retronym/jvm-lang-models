#!/usr/bin/env python3
"""Track T's oracle (packages/scala-types/docs/track-t.md): compile each program with each compiler setting
through the compile server, run it where accepted, and classify the outcome.

    soundness.py [--json OUT] [DIR]     (from the repository root; DIR defaults to probes/soundness)

A program is a `.scala` file in package `PKG`, with `AND` for the intersection type operator; the driver
writes `with` for Scala 2 and `&` for Scala 3, and a unique package per program and setting. Its `Main` is run
on the server's JVM. The sources contain no cast, type test or type pattern, so a `ClassCastException` is a
type-checker failure. Verdicts:

    rejected   the compiler reports an error (its first message)
    ok         runs to completion
    cce        java.lang.ClassCastException: accepted, and unsound
    expected   NotImplementedError (from ???) or NullPointerException (a null path dereferenced)
    other      any other throwable, or a timeout
"""
import importlib.util, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(ROOT, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)

SETTINGS = [
    ('2.12.21', '2.12.21', []),
    ('2.13.18', '2.13.18', []),
    ('3.9.0', '3.9.0', []),
    ('3.9.0 -source future', '3.9.0', ['-source', 'future']),
    ('3.9.0 -Yexplicit-nulls', '3.9.0', ['-Yexplicit-nulls']),
]


def render(text, pkg, version):
    return text.replace('PKG', pkg).replace(' AND ', ' with ' if version.startswith('2') else ' & ')


def classify(comp, run):
    if not comp['ok']:
        errs = compiler.errors(comp)
        msg = errs[0]['message'] if errs else comp.get('crash', 'crash')
        return 'rejected', ' '.join(msg.split())
    if run.get('timeout'):
        return 'other', 'timeout'
    exc = run.get('exception')
    if exc is None:
        return 'ok', run.get('stdout', '').strip()
    if exc.startswith('java.lang.ClassCastException'):
        return 'cce', exc
    if exc.startswith(('scala.NotImplementedError', 'java.lang.NullPointerException')):
        return 'expected', exc
    return 'other', exc


def main(argv):
    out = None
    if argv[:1] == ['--json']:
        out, argv = argv[1], argv[2:]
    d = argv[0] if argv else os.path.join(HERE, 'soundness')
    cases = sorted(f[:-len('.scala')] for f in os.listdir(d) if f.endswith('.scala'))
    results = []
    for si, (label, version, opts) in enumerate(SETTINGS):
        with compiler.scala(version) as server:
            for case in cases:
                pkg = f't{si}_{case}'
                src = render(open(os.path.join(d, case + '.scala')).read(), pkg, version)
                comp = server.compile(sources={f'{case}.scala': src}, options=opts)
                run = server.run(classpath=[comp['id']], main=f'{pkg}.Main') if comp['ok'] else {}
                verdict, detail = classify(comp, run)
                results.append({'case': case, 'setting': label, 'verdict': verdict, 'detail': detail})
                print(f'{label:24} {case:20} {verdict:9} {detail[:140]}', flush=True)
    if out:
        with open(out, 'w') as f:
            for r in results:
                f.write(json.dumps(r) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
