#!/usr/bin/env python3
"""Calibrate packages/scala-types/ScalaTypes/Members.lean (membership and overriding) against scalac and dotc.

    members.py OUT [--space flat] [--pool K] [--only 2.13] [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Runs `lake exe scalaprobe OUT` (which writes OUT/srcm/qN.scala and the model's verdicts
OUT/members-<dialect>.txt), or, with `--space flat`, `lake exe scalaprobe OUT flat` (the FlatRules space:
OUT/srcf/qN.scala, OUT/members-flat-<dialect>.txt, and OUT/flat-index.txt, which counts the configurations
each program stands for), then for each compiler, on K servers (`--pool`, default 1), each taking every
K-th program:

1. compiles each program on its own, in a compile server (packages/harness/scripts/compiler.py) that
   keeps one compiler warm, so an error in one program cannot stop another's refchecks;
2. maps each error to its program (the file), its class (the definition enclosing the error's line)
   and its kind (by message);
3. for the programs that compiled, runs a `Main` per program that prints, for each concrete class, which
   owner's `m` ran, in the server's `run` op (a throwaway class loader), so one bad program breaks only itself.

Writes OUT/members[-flat]-report-<dialect>.txt with every divergence grouped by shape, and
OUT/members[-flat]-actual-<dialect>.json with each program's errors and runs, and prints counts and times.
"""
import importlib.util, json, os, re, subprocess, sys, threading, time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))  # the repository root
_spec = importlib.util.spec_from_file_location('compiler', os.path.join(LEAN, 'packages', 'harness', 'scripts', 'compiler.py'))
compiler = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compiler)

KINDS = [  # (kind, substrings of scalac's or dotc's message)
    ('illegalModifiers', ['illegal combination of modifiers']),
    ('needsOverride', ['`override` modifier required', 'needs `override` modifier', "needs `override' modifier"]),
    ('conflicting', ['inherits conflicting members']),
    ('overridesNothing', ['overrides nothing']),
    ('finalOverride', ['cannot override final member']),
    ('accidental', ["third member that's overridden by both", 'third member that is overridden by both']),
    ('needsAbstract', ['needs to be abstract', 'object creation impossible']),
    ('stable', ['stable, immutable value']),
    ('weakerAccess', ['weaker access']),
    ('lazyMismatch', ['must be lazy', 'must not be lazy', 'declared lazy', 'non-lazy value']),
    ('resultType', ['incompatible type', 'is not a legal implementation of']),
    ('finalParent', ['illegal inheritance from final', 'cannot extend final class']),
    ('baseTypes', ['inherits different type instances', 'conflicting base types', "'s selftype"]),
]

DEF = re.compile(r'^(?:(?:abstract|final|sealed) )*(class|trait|object) (\w+)')


def classify(msg):
    if re.search(r'private \w+ \w+ cannot override', msg):  # dotc's form of weaker access
        return 'weakerAccess'
    for kind, subs in KINDS:
        if any(s in msg for s in subs):
            return kind
    return 'other:' + msg.strip().splitlines()[0][:80] if msg.strip() else 'other'


def enclosing_class(path, line):
    name = '?'
    with open(path) as f:
        for i, l in enumerate(f, 1):
            if i > line:
                break
            m = DEF.match(l)
            if m:
                name = m.group(2)
    return name


def verdicts(out, tag, server, pids=None, srcdir='srcm'):
    """Compile each program (or those in `pids`, in that order) in its own run; return ({pid: set((cls, kind))},
    accepted pids)."""
    src = os.path.join(out, srcdir)
    if pids is None:
        pids = sorted(f[:-len('.scala')] for f in os.listdir(src) if f.endswith('.scala'))
    errs, accepted = defaultdict(set), []
    for pid in pids:
        path = os.path.join(src, pid + '.scala')
        r = server.compile(files=[path], out=os.path.join(out, f'mclasses-{tag}', pid), id=pid)
        if 'crash' in r:
            raise SystemExit(f'{server.name}: crashed on {pid}:\n{r["crash"]}')
        found = compiler.errors(r)
        for d in found:
            errs[pid].add((enclosing_class(path, d['line']), classify(d['message'])))
        if not found:
            accepted.append(pid)
    return errs, accepted


OWNER_CODES = {'1': 'A', '2': 'B', '3': 'M', '4': 'C'}  # scalaprobe's `ownerCode`, for the flat space


def run_main(out, tag, server, accepted, news, srcdir='srcm'):
    """For each accepted program, compile it with a `Main_qN` that prints which owner's `m` ran for each
    concrete class, and run that in its own class loader; {pid: {cls: owner}}. In the flat space the classes
    take a type parameter (instantiated to `Any`) and `m` says its owner by its value or by printing `@owner`
    (`withOwners` in Harness/ScalaProbe.lean)."""
    flat = srcdir == 'srcf'
    d = os.path.join(out, f'mrun-{tag}')
    os.makedirs(d, exist_ok=True)
    server.recycle()  # the programs' packages again, in a fresh compiler
    ran = defaultdict(dict)
    with open(os.path.join(d, f'log-{server.name.split()[-1]}-{threading.get_ident()}.txt'), 'w') as log:
        for pid in accepted:
            if flat:
                calls = '\n'.join(f'    try {{ val o = new {pid}.{c}[Any](); print("{pid} {c} "); println(o.m) }} catch {{ case e: Throwable => println("!" + e.getClass.getSimpleName) }}'
                                  for c in news.get(pid, []))
            else:
                calls = '\n'.join(f'    try println("{pid} {c} " + new {pid}.{c}().m) catch {{ case e: Throwable => println("{pid} {c} !" + e.getClass.getSimpleName) }}'
                                  for c in news.get(pid, []))
            main = f'object Main_{pid} {{\n  def main(args: Array[String]): Unit = {{\n{calls}\n  }}\n}}\n'
            r = server.compile(files=[os.path.join(out, srcdir, pid + '.scala')], sources={f'Main_{pid}.scala': main},
                               out=os.path.join(d, pid), id=f'run-{pid}')
            if not r['ok']:
                raise SystemExit(f'{server.name}: {pid} with its Main failed to compile: {r}')
            x = server.run([r['id']], main=f'Main_{pid}', timeout=10)
            log.write(f'{pid}\t{json.dumps(x)}\n')
            if not x['ok']:
                raise SystemExit(f'{server.name}: Main_{pid} failed, see {log.name}')
            for line in x['stdout'].splitlines():
                parts = line.split()
                if len(parts) >= 3 and parts[0] == pid:
                    o = parts[2]
                    if flat:
                        o = o[1:] if o.startswith('@') else OWNER_CODES.get(o, o)
                    ran[pid][parts[1]] = o
    return ran


def read_model(path):
    errs, runs = defaultdict(set), defaultdict(dict)
    for line in open(path):
        parts = line.rstrip('\n').split('\t')
        if len(parts) != 4:
            continue
        pid, what, cls, x = parts
        if what == 'err':
            errs[pid].add((cls, x))
        else:
            runs[pid][cls] = x
    return errs, runs


def show(errs):
    return ' '.join(sorted(f'{c}:{k}' for c, k in errs)) or 'ok'


def calibrate(out, tag, version, space, pool, merrs, mruns):
    """Compile (and run) every program of the space on `pool` servers; ({pid: errors}, accepted, {pid: runs})."""
    srcdir, sfx = ('srcf', '-flat') if space == 'flat' else ('srcm', '')
    src = os.path.join(out, srcdir)
    pids = sorted((f[:-len('.scala')] for f in os.listdir(src) if f.endswith('.scala')), key=lambda p: int(p[1:]))
    results, failures = [None] * pool, []

    def work(i):
        try:
            mine = pids[i::pool]
            with compiler.scala(version, work=os.path.join(out, f'server{sfx}-{tag}-{i}')) as server:
                errs, acc = verdicts(out, f'{tag}{sfx}', server, mine, srcdir)
                news = {pid: list(mruns.get(pid, {}).keys()) for pid in acc if not merrs.get(pid)}
                ran = run_main(out, f'{tag}{sfx}', server, [p for p in acc if p in news], news, srcdir)
            results[i] = (errs, acc, ran)
        except BaseException as e:  # noqa: BLE001 - reported below
            failures.append(e)

    threads = [threading.Thread(target=work, args=(i,)) for i in range(pool)]
    for t in threads: t.start()
    for t in threads: t.join()
    if failures:
        raise failures[0]
    errs, acc, ran = defaultdict(set), [], {}
    for e, a, r in results:
        errs.update(e); acc += a; ran.update(r)
    return errs, acc, ran


def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0] if args else 'out')
    versions = {'2.12': '2.12.21', '2.13': '2.13.18', '3': '3.9.0'}
    space, pool, only = 'members', 1, None
    for i, a in enumerate(args):
        if a == '--scala212': versions['2.12'] = args[i + 1]
        if a == '--scala2': versions['2.13'] = args[i + 1]
        if a == '--scala3': versions['3'] = args[i + 1]
        if a == '--space': space = args[i + 1]
        if a == '--pool': pool = int(args[i + 1])
        if a == '--only': only = args[i + 1]
    if only:
        versions = {only: versions[only]}
    flat = space == 'flat'
    sfx = '-flat' if flat else ''
    if not os.path.isdir(os.path.join(out, 'srcf' if flat else 'srcm')):
        subprocess.run(['lake', 'exe', 'scalaprobe', out] + (['flat'] if flat else []), cwd=LEAN, check=True)
    weight, desc = {}, {}
    for l in open(os.path.join(out, 'flat-index.txt' if flat else 'members-index.txt')):
        if not l.strip():
            continue
        parts = l.rstrip('\n').split('\t')
        desc[parts[0]] = parts[-1]
        weight[parts[0]] = int(parts[1]) if flat else 1
    for tag, version in versions.items():
        merrs, mruns = read_model(os.path.join(out, f'members{sfx}-{tag}.txt'))
        t0 = time.time()
        aerrs, accepted, ran = calibrate(out, tag, version, space, pool, merrs, mruns)
        secs = time.time() - t0
        with open(os.path.join(out, f'members{sfx}-actual-{tag}.json'), 'w') as f:
            json.dump({p: {'errs': sorted(map(list, aerrs.get(p, ()))), 'runs': ran.get(p, {})} for p in desc}, f)
        groups = defaultdict(list)
        agree = 0
        for pid in desc:
            e, a = merrs.get(pid, set()), aerrs.get(pid, set())
            if e != a:
                groups[f'errors model [{show(e)}] scalac [{show(a)}]'].append(pid)
            elif not e and ran.get(pid, {}) != mruns.get(pid, {}):
                groups[f'runs model {sorted(mruns.get(pid, {}).items())} scalac {sorted(ran.get(pid, {}).items())}'].append(pid)
            else:
                agree += 1
        cfgs = sum(weight.values())
        cagree = cfgs - sum(weight[p] for ps in groups.values() for p in ps)
        line = f'scalac {version}: {agree}/{len(desc)} programs agree; {len(accepted)} accepted; {len(groups)} divergence shapes'
        if flat:
            line += f'; {cagree}/{cfgs} configurations'
        print(f'{line}; {secs:.0f} s on {pool} server(s), {1000 * secs * pool / len(desc):.1f} ms/program/server', flush=True)
        with open(os.path.join(out, f'members{sfx}-report-{tag}.txt'), 'w') as rep:
            rep.write(line + '\n\n')
            for d, pids in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                rep.write(f'{len(pids):5d}  {d}\n       e.g. ' + '; '.join(f'{p}: {desc[p]}' for p in pids[:3]) + '\n')


if __name__ == '__main__':
    main()
