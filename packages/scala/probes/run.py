#!/usr/bin/env python3
"""Run the Scala catalogue (packages/scala/Scala/Catalogue.lean) on HotSpot and compare with the model.

    run.py OUT [--scala 2.13.18] JAVA_HOME...   (from the repository root)

`lake exe bincompat scala OUT` writes each case's library (v0, v1) and client sources, in package `p`,
and its sites and the model's outcomes before and after. Each case is compiled with scalac in the compile
server (packages/harness/scripts/compiler.py): v0, the client against v0, and v1. The classfiles are
instrumented with `ProbeLog` calls (packages/jvm/probes/Instrument.java), the sites rendered by
packages/jvm/probes/Render.java, and packages/jvm/probes/Run.java runs the client against v0 and v1 on
each JDK and compares the `Throwable` or the sequence of methods entered with the model's. Cases that do not
compile with the given scalac (the Scala 3 ones, with Scala 2) are skipped.
"""
import importlib.util, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
PROBES = os.path.join(ROOT, 'packages', 'jvm', 'probes')
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(ROOT, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)
RENDER_JAVA_HOME = os.environ.get('RENDER_JAVA_HOME', os.path.expanduser('~/.sdkman/candidates/java/25.0.4-tem'))


def own(n):
    return not n.startswith(('scala/', 'java/'))


def qual(n):
    """A model class name as the binary name of the class scalac emits in package `p`."""
    return 'p.' + n if own(n) else n.replace('/', '.')


def qdesc(d):
    return re.sub(r'L([^;]+);', lambda m: 'L' + ('p/' + m[1] if own(m[1]) else m[1]) + ';', d)


def qsite(s):
    s = dict(s)
    for k in ('owner', 'recv', 'cls'):
        if k in s:
            s[k] = qual(s[k])
    if 'desc' in s:
        s['desc'] = qdesc(s['desc'])
    if 'site' in s:
        s['site'] = qsite(s['site'])
    return s


def qcase(k):
    k['loads'] = [qual(x) for x in k['loads']]
    k['sites'] = [qsite(s) for s in k['sites']]
    # the standard library is not instrumented, so only the program's own classes are seen to run
    for w in ('before', 'after'):
        if 'ok' in k[w]:
            k[w]['ok'] = [qual(x) for x in k[w]['ok'] if own(x)]
    return k


def ctors(cls, *cp):
    """The constructor descriptors of the compiled class `cls` (a model name), by `javap`."""
    javap = os.path.join(RENDER_JAVA_HOME, 'bin', 'javap')
    r = subprocess.run([javap, '-s', '-p', '-cp', os.pathsep.join(cp), qual(cls)], capture_output=True, text=True)
    lines = r.stdout.splitlines()
    return [lines[i + 1].split('descriptor:')[1].strip() for i, l in enumerate(lines)
            if re.search(r'\b' + re.escape(qual(cls)) + r'\(', l) and i + 1 < len(lines)]


def receiver(site, *cp):
    """A Scala client gets a module class's instance from `MODULE$`, and builds another class with one of
    its constructors: `Render`'s `new R()` only where `R` has a public `()V`. The model's receiver is any
    instance of `R`, so this is the program it describes."""
    if 'site' in site:
        return receiver(site['site'], *cp)
    r = site.get('recv')
    if r is None or not own(r):
        return
    if r.endswith('$'):
        site['recvModule'] = True
        return
    cs = ctors(r, *cp)
    if cs and '()V' not in cs:
        site['recvCtor'] = cs[0]


def main(argv):
    version = '2.13.18'
    if '--scala' in argv:
        i = argv.index('--scala')
        version = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    out, jdks = os.path.abspath(argv[0]), argv[1:]
    os.makedirs(out, exist_ok=True)
    tsv = subprocess.run(['lake', 'exe', 'bincompat', 'scala', out], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    names = [l.split('\t')[0] for l in tsv.splitlines() if l.strip()]
    cases = []
    with compiler.scala(version) as s:
        for n in names:
            d = os.path.join(out, n)
            r0 = s.compile(files=[os.path.join(d, 'v0.scala')], out=os.path.join(d, 'v0'))
            rc = s.compile(files=[os.path.join(d, 'client.scala')], classpath=[os.path.join(d, 'v0')], out=os.path.join(d, 'client'))
            r1 = s.compile(files=[os.path.join(d, 'v1.scala')], out=os.path.join(d, 'v1'))
            if not (r0['ok'] and rc['ok'] and r1['ok']):
                print(f'scalac {version}: {n} does not compile, skipped', file=sys.stderr)
                continue
            k = json.load(open(os.path.join(d, 'case.json')))
            if any('lowering' in k[w] for w in ('before', 'after')):
                print(f'{n}: the model does not lower it, skipped', file=sys.stderr)
                continue
            for site in k['sites']:
                receiver(site, os.path.join(d, 'client'), os.path.join(d, 'v0'))
            cases.append(qcase(k))
    jsonl = os.path.join(out, 'cases.jsonl')
    with open(jsonl, 'w') as f:
        for k in cases:
            f.write(json.dumps(k) + '\n')
    tools = os.path.join(out, '.tools')
    javac = os.path.join(RENDER_JAVA_HOME, 'bin', 'javac')
    java = os.path.join(RENDER_JAVA_HOME, 'bin', 'java')
    subprocess.run([javac, '-d', tools] + [os.path.join(PROBES, f) for f in ('Render.java', 'Json.java', 'Instrument.java')], check=True)
    subprocess.run([java, '-cp', tools, 'Instrument', 'p/'] +
                   [os.path.join(out, k['name'], w) for k in cases for w in ('v0', 'v1', 'client')], check=True)
    subprocess.run([java, '-cp', tools, 'Render', jsonl, out], check=True)
    run = os.path.join(out, '.run')
    subprocess.run([javac, '--release', '17', '-d', run] + [os.path.join(PROBES, f) for f in ('Run.java', 'Json.java', 'ProbeLog.java')], check=True)
    cp = os.pathsep.join([run] + compiler.library(version))
    status = 0
    for jh in jdks:
        r = subprocess.run([os.path.join(jh, 'bin', 'java'), '-cp', cp, 'Run', jsonl, out], capture_output=True, text=True)
        sys.stdout.write('\n'.join(l for l in r.stdout.splitlines() if not l.startswith('#json ')) + '\n')
        sys.stderr.write(r.stderr)
        status |= r.returncode
    return status


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
