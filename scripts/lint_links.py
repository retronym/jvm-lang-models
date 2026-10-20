"""Cross-links in the Markdown documents.

Checks every `.md` file outside `.lake/` and fails on:

* a broken relative link: `[text](path)` whose target file does not exist;
* a mention that could be a link but is not:
  - a backticked path to a file or directory of this repository, relative to the document, its
    package or the repository root (`docs/status.md`, `packages/jvm/Jvm/Link.lean`, `Jvm/Link.lean`
    inside the `jvm` package), optionally with a line (`General.lean:108`); a bare file name
    without a directory only when it is in the document's own directory;
  - a backticked Lean file name that names exactly one file in the repository (`Erasure.lean`);
  - a GitHub reference `owner/repo#N`, or one of the short forms the documents use
    (`talks#N`, `scala3#N`, `rz#N` for retronym/zinc, `sz#N` for sbt/zinc);
  - a backticked Lean declaration (`zinc_diverges`, `XCompiler.round_preserves`) that names
    exactly one `theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive` or `class` by a
    suffix of its full name; it is linked to its line. The name must contain `_` or `.`, or be
    CamelCase with two capitals (`XCompiler`), so that ordinary words are left alone;
* a link to a Lean declaration whose line anchor is out of date (the declaration moved);
* a line number written by hand (`General.lean:108`) outside `docs/history/`: it drifts as the
  file changes, so name the declaration instead. In `docs/history/` such references are kept as
  written and linked to the file without a line.

With `--fix` it rewrites those mentions into links in place, relative to the file, and reports
what it could not fix. The drafts in `docs/upstream/` (not its index) are pasted into issue
trackers, so there links are absolute, to this repository on GitHub at the commit checked out when
`--fix` ran (`REPO_URL`); a declaration's absolute link is accepted at any commit, its line being
that commit's. Fenced code blocks, inline code that is not a path, and existing links are
left alone. A name that matches several files (`Lower.lean`) is not linked.

Usage: python3 -I scripts/lint_links.py [--fix]
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO_URL = 'https://github.com/retronym/jvm-lang-models/blob/'
_rev = None


def standalone(md):
    """Is `md` a draft read outside the repository, whose links must be absolute?"""
    return md.startswith('docs/upstream/') and os.path.basename(md) != 'README.md'


def rev():
    """The commit absolute links point at: the one checked out."""
    global _rev
    if _rev is None:
        _rev = subprocess.run(['git', 'rev-parse', '--short=10', 'HEAD'], cwd=ROOT,
                              capture_output=True, text=True).stdout.strip() or 'main'
    return _rev

SHORT = {
    'talks': 'retronym/talks',
    'scala3': 'scala/scala3',
    'rz': 'retronym/zinc',
    'sz': 'sbt/zinc',
}


def repo_files():
    out = []
    for d, dirs, fs in os.walk(ROOT):
        dirs[:] = [x for x in dirs if x not in ('.lake', '.git', '.scala-build', '.bsp')]
        for f in fs:
            out.append(os.path.relpath(os.path.join(d, f), ROOT))
    return out


FILES = repo_files()
FILESET = set(FILES)
DIRS = {os.path.dirname(f) for f in FILES}
for f in list(DIRS):
    while f:
        f = os.path.dirname(f)
        DIRS.add(f)
BY_BASE = {}
for f in FILES:
    BY_BASE.setdefault(os.path.basename(f), []).append(f)


def package_root(path):
    """The nearest ancestor directory of `path` with a lakefile, as a repository path."""
    d = os.path.dirname(path)
    while d:
        if os.path.join(d, 'lakefile.toml') in FILESET:
            return d
        d = os.path.dirname(d)
    return ''


def resolve(md, target):
    """A repository path for `target` as written in `md`, or None."""
    target = target.rstrip('/')
    if not target or target.startswith(('http:', 'https:', '#', 'mailto:')):
        return None
    cands = [os.path.normpath(os.path.join(os.path.dirname(md), target))]
    if '/' in target:
        # a path: relative to the document, its package, or the repository root
        pkg = package_root(md)
        if pkg:
            cands.append(os.path.normpath(os.path.join(pkg, target)))
        cands.append(os.path.normpath(target))
    # a bare name (`lakefile.toml`, `README.md`) only in the document's own directory: elsewhere
    # it usually means "each package's", not the root's
    for c in cands:
        if c in FILESET or c in DIRS:
            return c
    if '/' not in target and target.endswith('.lean'):
        hits = BY_BASE.get(target, [])
        if len(hits) == 1:
            return hits[0]
    return None


def rel(md, path):
    if standalone(md):
        return REPO_URL + rev() + '/' + path
    r = os.path.relpath(path, os.path.dirname(md) or '.')
    return r


def repo_path(href):
    """The repository path of an absolute link to this repository, or None."""
    if not href.startswith(REPO_URL):
        return None
    return href[len(REPO_URL):].split('/', 1)[1].split('#')[0]


DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|nonrec|unsafe)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s:({\[]+)')
NS_OPEN = re.compile(r'^\s*namespace\s+(\S+)')
NS_END = re.compile(r'^\s*end\s+(\S+)\s*$')


def lean_decls():
    """Each declaration's dotted suffixes, to the set of (file, line) that define it."""
    by_suffix = {}
    for f in FILES:
        if not f.endswith('.lean'):
            continue
        ns = []
        for n, line in enumerate(open(os.path.join(ROOT, f), encoding='utf-8'), 1):
            m = NS_OPEN.match(line)
            if m:
                ns += m.group(1).split('.')
                continue
            m = NS_END.match(line)
            if m:
                k = len(m.group(1).split('.'))
                if ns[-k:] == m.group(1).split('.'):
                    del ns[-k:]
                continue
            m = DECL.match(line)
            if m:
                parts = ns + m.group(2).split('.')
                for i in range(len(parts)):
                    by_suffix.setdefault('.'.join(parts[i:]), set()).add((f, n))
    return by_suffix


DECLS = lean_decls()
IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)`")


def decl_target(name):
    if not ('_' in name or '.' in name or re.fullmatch(r'[A-Z][a-z0-9]*[A-Z][A-Za-z0-9]*', name)):
        return None
    hits = DECLS.get(name)
    return next(iter(hits)) if hits and len(hits) == 1 else None


CODE_PATH = re.compile(r'`([A-Za-z0-9_./-]+?\.(?:lean|md|py|sh|java|scala|toml|yml)|[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)+/?)(?::(\d+))?`')
GH_FULL = re.compile(r'(?<![\w/\[.-])([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)#(\d+)\b')
GH_SHORT = re.compile(r'(?<![\w/\[.-])(' + '|'.join(SHORT) + r')#(\d+)\b')
LINK = re.compile(r'\[[^\]]*\]\([^)]*\)')
INLINE_CODE = re.compile(r'`[^`]*`')


def protected_spans(line):
    """Spans that must not be rewritten: existing links."""
    return [m.span() for m in LINK.finditer(line)]


def inside(pos, spans):
    return any(a <= pos < b for a, b in spans)


def process(md, text, fix):
    problems = []
    out = []
    fence = False
    for n, line in enumerate(text.split('\n'), 1):
        if line.lstrip().startswith('```'):
            fence = not fence
            out.append(line)
            continue
        if fence:
            out.append(line)
            continue
        # broken links (not inside inline code)
        code0 = [c.span() for c in INLINE_CODE.finditer(line)]
        for m in re.finditer(r'\]\(([^)\s]+)\)', line):
            if inside(m.start(), code0):
                continue
            t = m.group(1).split('#')[0]
            if not t or t.startswith(('http:', 'https:', 'mailto:')):
                continue
            p = os.path.normpath(os.path.join(os.path.dirname(md), t))
            if p not in FILESET and p not in DIRS:
                problems.append(f'{md}:{n}: broken link to {m.group(1)}')
        spans = protected_spans(line)
        codes = [m.span() for m in INLINE_CODE.finditer(line)]

        history = md.startswith('docs/history/')
        if not history:
            for m in re.finditer(r'`[^`]+\.lean:\d+`', line):
                problems.append(f'{md}:{n}: line number written by hand in {m.group(0)}: '
                                f'name the declaration instead (its link keeps the line current)')

        def code_path(m):
            if inside(m.start(), spans) or (m.start() > 0 and line[m.start() - 1] == '['):
                return m.group(0)
            p = resolve(md, m.group(1))
            if p is None:
                return m.group(0)
            # a written line number drifts; in history documents link the file only
            href = rel(md, p) + (f'#L{m.group(2)}' if m.group(2) and not history else '')
            problems.append(f'{md}:{n}: unlinked path {m.group(0)}')
            return f'[{m.group(0)}]({href})'

        line2 = CODE_PATH.sub(code_path, line)
        spans = protected_spans(line2)
        codes = [m.span() for m in INLINE_CODE.finditer(line2)]

        def gh(m, repo):
            if inside(m.start(), spans) or inside(m.start(), codes):
                return m.group(0)
            problems.append(f'{md}:{n}: unlinked reference {m.group(0)}')
            return f'[{m.group(0)}](https://github.com/{repo}/issues/{m.group(2)})'

        line2 = GH_FULL.sub(lambda m: gh(m, m.group(1)) if '.' not in m.group(1).split('/')[0] else m.group(0), line2)
        spans = protected_spans(line2)
        codes = [m.span() for m in INLINE_CODE.finditer(line2)]
        line2 = GH_SHORT.sub(lambda m: gh(m, SHORT[m.group(1)]), line2)

        # Lean declarations: stale anchors on existing links, then unlinked names
        def anchor(m):
            name, href = m.group(1), m.group(2)
            t = decl_target(name)
            if t is None or not href.split('#')[0].endswith('.lean'):
                return m.group(0)
            want = f'{rel(md, t[0])}#L{t[1]}'
            # an absolute link pins a commit: its line is that commit's, so only the file is checked
            if standalone(md) and repo_path(href) == t[0]:
                return m.group(0)
            if href != want:
                problems.append(f'{md}:{n}: stale link to {name} ({href}, now {want})')
                return f'[`{name}`]({want})'
            return m.group(0)

        line2 = re.sub(r'\[`([A-Za-z_][A-Za-z0-9_\'.]*)`\]\(([^)]+)\)', anchor, line2)
        spans = protected_spans(line2)

        def decl(m):
            if inside(m.start(), spans) or (m.start() > 0 and line2[m.start() - 1] == '['):
                return m.group(0)
            t = decl_target(m.group(1))
            if t is None:
                return m.group(0)
            problems.append(f'{md}:{n}: unlinked declaration {m.group(0)}')
            return f'[{m.group(0)}]({rel(md, t[0])}#L{t[1]})'

        line2 = IDENT.sub(decl, line2)
        out.append(line2 if fix else line)
    return '\n'.join(out), problems


def main():
    fix = '--fix' in sys.argv
    problems = []
    for f in sorted(FILES):
        if not f.endswith('.md'):
            continue
        text = open(os.path.join(ROOT, f), encoding='utf-8').read()
        new, ps = process(f, text, fix)
        problems += ps
        if fix and new != text:
            open(os.path.join(ROOT, f), 'w', encoding='utf-8').write(new)
    if fix:
        _, problems = zip(*[process(f, open(os.path.join(ROOT, f), encoding='utf-8').read(), False)
                            for f in sorted(FILES) if f.endswith('.md')]) or ([], [])
        problems = [p for ps in problems for p in ps]
    print('\n'.join(problems) if problems else 'links ok')
    sys.exit(1 if problems else 0)


if __name__ == '__main__':
    main()
