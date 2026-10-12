"""Client for the compile servers in packages/harness/server (see packages/harness/docs/compile-server.md).

    import compiler
    with compiler.javac('/path/to/jdk17') as s:
        r = s.compile(sources={'p1/A.java': '...'}, options=['--release', '17'])
        r['ok'], r['diagnostics'], r['out'], r['classes']
    with compiler.scala('2.13.18') as s:          # scalac 2 (2.12, 2.13) or dotc (3.x), by version
        r = s.compile(files=['/abs/q1.scala'])
        s.run(classpath=[r['id']], main='Main')['stdout']

One JVM per compiler version (per JDK for javac). The servers are built on first use into
packages/harness/server/.build, keyed by a digest of their sources and the compiler; compilers come from
coursier, pinned by version, as the probes' scala-cli runs do. A server that dies (a crash, or a run that timed
out) is restarted and the request resent once.
"""
import hashlib, itertools, json, os, shutil, subprocess, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SERVER = os.path.normpath(os.path.join(HERE, '..', 'server'))
BUILD = os.path.join(SERVER, '.build')
JAVA_SOURCES = ['Json.java', 'Backend.java', 'Server.java', 'JavacBackend.java']


def _digest(paths, *extra):
    h = hashlib.sha256()
    for p in paths:
        h.update(open(p, 'rb').read())
    for e in extra:
        h.update(e.encode())
    return h.hexdigest()[:12]


def coursier_cp(*deps):
    r = subprocess.run(['coursier', 'fetch', '--classpath'] + list(deps), capture_output=True, text=True, check=True)
    return r.stdout.strip().split(os.pathsep)


def default_java_home():
    """The JDK whose `java` is on PATH."""
    r = subprocess.run(['java', '-XshowSettings:properties', '-version'], capture_output=True, text=True)
    for line in r.stderr.splitlines():
        if line.strip().startswith('java.home ='):
            return line.split('=', 1)[1].strip()
    raise SystemExit('no java on PATH')


def _build(name, key, build):
    """Build into BUILD/name-key once; `build(dir)` writes the classes. Atomic, so concurrent probes are safe."""
    dest = os.path.join(BUILD, f'{name}-{key}')
    if os.path.isdir(dest):
        return dest
    os.makedirs(BUILD, exist_ok=True)
    tmp = tempfile.mkdtemp(dir=BUILD, prefix=f'.{name}-')
    try:
        build(tmp)
        os.rename(tmp, dest)
    except OSError:
        if not os.path.isdir(dest):
            raise
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return dest


def java_classes(java_home):
    """The server's Java part, compiled for release 17 by the given JDK."""
    srcs = [os.path.join(SERVER, f) for f in JAVA_SOURCES]
    def build(d):
        subprocess.run([os.path.join(java_home, 'bin', 'javac'), '--release', '17', '-nowarn', '-d', d] + srcs,
                       check=True)
    return _build('java', _digest(srcs, java_home), build)


def scala_classes(version, java_home):
    """The scalac 2 or dotc backend, compiled by that compiler against the server's Java part."""
    jcls = java_classes(java_home)
    if version.startswith('3'):
        srcs = [os.path.join(SERVER, 'DotcBackend.scala')]
        cp = coursier_cp(f'org.scala-lang:scala3-compiler_3:{version}')
        main = 'dotty.tools.dotc.Main'
    else:
        binary = '.'.join(version.split('.')[:2])
        srcs = [os.path.join(SERVER, 'ScalacBackend.scala'), os.path.join(SERVER, f'Compat_{binary}.scala')]
        cp = coursier_cp(f'org.scala-lang:scala-compiler:{version}')
        main = 'scala.tools.nsc.Main'
    def build(d):
        subprocess.run([os.path.join(java_home, 'bin', 'java'), '-cp', os.pathsep.join(cp), main,
                        '-classpath', os.pathsep.join(cp + [jcls]), '-d', d] + srcs, check=True)
    return _build(f'scala-{version}', _digest(srcs + [os.path.join(SERVER, f) for f in JAVA_SOURCES], version, java_home),
                  build), cp, jcls


def library(version):
    """The classpath a program compiles and runs against, as scala-cli gives it."""
    if version.startswith('3'):
        return coursier_cp(f'org.scala-lang:scala3-library_3:{version}')
    return coursier_cp(f'org.scala-lang:scala-library:{version}')


class Server:
    def __init__(self, cmd, name, work):
        self.cmd, self.name, self.work = cmd, name, work
        self.proc = None
        self.ids = itertools.count(1)
        self.starts = 0
        self.log = open(os.path.join(work, 'server.log'), 'a')

    def _start(self):
        self.starts += 1
        self.proc = subprocess.Popen(self.cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.log,
                                     text=True, encoding='utf-8', bufsize=1)

    def request(self, req):
        req = dict(req)
        req.setdefault('id', f'r{next(self.ids)}')
        line = json.dumps(req) + '\n'
        for attempt in (0, 1):
            if self.proc is None or self.proc.poll() is not None:
                self._start()
            try:
                self.proc.stdin.write(line)
                self.proc.stdin.flush()
                resp = self.proc.stdout.readline()
            except BrokenPipeError:
                resp = ''
            if resp:
                return json.loads(resp)
            self.proc.wait()
            self.proc = None
        raise RuntimeError(f'{self.name}: no response to {req["id"]}, see {self.log.name}')

    def compile(self, sources=None, files=None, options=(), classpath=(), out=None, id=None):
        """Compile one program. `sources` maps file names to text; `files` are paths the server reads. A
        diagnostic's `file` is the name or path as given."""
        req = {'op': 'compile', 'sources': sources or {}, 'files': list(files or []), 'options': list(options),
               'classpath': list(classpath)}
        if out: req['out'] = out
        if id: req['id'] = id
        return self.request(req)

    def run(self, classpath, main='Main', args=(), timeout=10.0, id=None):
        """Load `classpath` (ids of earlier compiles, or directories) in a throwaway class loader over the
        library, invoke `main`, and capture stdout and stderr."""
        req = {'op': 'run', 'classpath': list(classpath), 'main': main, 'args': list(args),
               'timeout': int(timeout * 1000)}
        if id: req['id'] = id
        return self.request(req)

    def recycle(self):
        return self.request({'op': 'recycle'})

    def close(self):
        if self.proc and self.proc.poll() is None:
            self.proc.stdin.close()
            self.proc.wait()
        self.proc = None
        self.log.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


JVM_OPTS = ['-Xss8m', '-Xmx3g', '-XX:+UseParallelGC']


def _work(work, name):
    work = work or tempfile.mkdtemp(prefix=f'compile-server-{name}-')
    os.makedirs(work, exist_ok=True)
    return os.path.abspath(work)


def javac(java_home, work=None, recycle=1000):
    """A javac server running on (and compiling with) the JDK at `java_home`."""
    work = _work(work, 'javac')
    cmd = [os.path.join(java_home, 'bin', 'java')] + JVM_OPTS + ['-cp', java_classes(java_home),
           'compileserver.Server', '--backend', 'compileserver.JavacBackend', '--work', work,
           '--recycle', str(recycle)]
    return Server(cmd, f'javac {java_home}', work)


def scala(version, work=None, recycle=1000, java_home=None):
    """A scalac 2 (2.12.x, 2.13.x) or dotc (3.x) server for `version`, running on `java_home` (default: the
    `java` on PATH)."""
    java_home = java_home or default_java_home()
    work = _work(work, f'scala-{version}')
    backend, cp, jcls = scala_classes(version, java_home)
    kind = 'DotcBackend' if version.startswith('3') else 'ScalacBackend'
    cmd = [os.path.join(java_home, 'bin', 'java')] + JVM_OPTS + ['-cp', os.pathsep.join([jcls, backend] + cp),
           'compileserver.Server', '--backend', f'compileserver.{kind}', '--work', work, '--recycle', str(recycle),
           '--', '--library', os.pathsep.join(library(version))]
    return Server(cmd, f'scala {version}', work)


def errors(resp):
    """The error diagnostics of a compile response."""
    return [d for d in resp.get('diagnostics', []) if d['severity'] == 'ERROR']
