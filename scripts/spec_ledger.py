"""The specification ledger: `docs/specification-ledger.md`, generated from the `Spec:` tags in the
Lean sources' docstrings (the convention is in `docs/specification.md`, "The specification
ledger").

A tag is a line of a declaration's docstring (`/-- … -/`) that starts with `Spec:`, and runs on to
the next tag, a blank line or the end of the docstring:

    Spec: cites JVMS §5.4.3.3, JVMS §5.4.3.4
    Spec: unspecified JVMS §5.3.5: <evidence>
    Spec: contradicts SLS §5.1.4 / scalac 2.13.18, dotc 3.9.0: <witness>

A clause is a specification (`JVMS`, `JLS`, `SLS`) and an optional section (`§5.4.3.3`), with
words after it as a note (`JVMS §6.5 invokeinterface`). The page lists, per specification and
section, the declarations that cite it, the omissions with their evidence, and the contradictions
with their witnesses, each linked to its declaration. Backticked declaration names in the text are
linked as `scripts/lint_links.py` links them.

Usage: python3 -I scripts/spec_ledger.py [--check]
"""
import importlib.util
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = 'docs/specification-ledger.md'
_spec = importlib.util.spec_from_file_location('lint_links', os.path.join(ROOT, 'scripts', 'lint_links.py'))
lint_links = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lint_links)

SPECS = {
    'JVMS': 'The Java Virtual Machine Specification, Java SE 25',
    'JLS': 'The Java Language Specification, Java SE 25',
    'SLS': 'The Scala Language Specification (Scala 2.13, and Scala 3 where it differs)',
}
KINDS = ('cites', 'unspecified', 'contradicts')
CLAUSE = re.compile(r'\b(JVMS|JLS|SLS)\b(?:\s*§\s*([0-9]+(?:\.[0-9]+)*))?')
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|nonrec|unsafe)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b\s*([^\s:({\[]*)')


def lean_files():
    for d, dirs, fs in os.walk(os.path.join(ROOT, 'packages')):
        dirs[:] = [x for x in dirs if x not in ('.lake', '.git')]
        for f in sorted(fs):
            if f.endswith('.lean'):
                yield os.path.relpath(os.path.join(d, f), ROOT)


def docstrings(path):
    """Each declaration docstring of `path`: (text, the declaration's full name or None, its line)."""
    lines = open(os.path.join(ROOT, path), encoding='utf-8').read().split('\n')
    ns, out, i = [], [], 0
    while i < len(lines):
        line = lines[i]
        m = lint_links.NS_OPEN.match(line)
        if m:
            ns += m.group(1).split('.')
        m = lint_links.NS_END.match(line)
        if m:
            k = len(m.group(1).split('.'))
            if ns[-k:] == m.group(1).split('.'):
                del ns[-k:]
        s = line.lstrip()
        if s.startswith('/--'):
            body = [s[3:]]
            while '-/' not in body[-1] and i + 1 < len(lines):
                i += 1
                body.append(lines[i])
            body[-1] = body[-1][:body[-1].index('-/')]
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or lines[j].lstrip().startswith('set_option')
                                      or (lines[j].lstrip().startswith('@[') and not DECL.match(lines[j]))):
                j += 1
            d = DECL.match(lines[j]) if j < len(lines) else None
            name = None
            if d and d.group(1) not in ('example', 'instance') and d.group(2):
                name = '.'.join(ns + d.group(2).split('.'))
            out.append(('\n'.join(body), name, j + 1, d.group(1) if d else None))
        i += 1
    return out


def tags(text):
    """The `Spec:` tags of a docstring, each as one string; and the text before the first."""
    lead, cur, found = [], None, []
    for raw in text.split('\n'):
        line = raw.strip()
        if line.startswith('Spec:'):
            if cur is not None:
                found.append(cur)
            cur = line[5:].strip()
        elif cur is not None:
            if not line:
                found.append(cur)
                cur = None
            else:
                cur += ' ' + line
        elif not found:
            lead.append(line)
    if cur is not None:
        found.append(cur)
    return ' '.join(x for x in lead if x), found


def summary(lead):
    """The docstring's first sentence."""
    m = re.match(r'(.+?[.:])(\s|$)', lead)
    s = (m.group(1) if m else lead).strip()
    return s[:-1] if s.endswith(':') else s


def clauses(s):
    return [(m.group(1), m.group(2) or '') for m in CLAUSE.finditer(s)]


def parse(tag, where):
    kind = tag.split(None, 1)[0] if tag else ''
    if kind not in KINDS:
        raise SystemExit(f'{where}: a Spec tag must start with one of {", ".join(KINDS)}: {tag!r}')
    rest = tag[len(kind):].strip()
    if kind == 'cites':
        cs = clauses(rest)
        if not cs:
            raise SystemExit(f'{where}: `cites` names no clause: {tag!r}')
        return [(kind, c, '') for c in cs]
    head, sep, text = rest.partition(': ')
    if not sep:
        raise SystemExit(f'{where}: `{kind}` needs `: ` and its {"evidence" if kind == "unspecified" else "witness"}: {tag!r}')
    cs = clauses(head)
    if not cs:
        raise SystemExit(f'{where}: `{kind}` names no specification before the colon: {tag!r}')
    if kind == 'contradicts' and '/' not in head:
        raise SystemExit(f'{where}: `contradicts` names two sources, `a / b`: {tag!r}')
    note = head.strip() if kind == 'contradicts' else ''
    return [(kind, c, (note + ': ' if note else '') + text.strip()) for c in cs]


def rebase(text, path):
    """Relative Markdown links in a docstring are relative to its Lean file; make them relative to `docs/`."""
    def fix(m):
        t, frag = m.group(1), m.group(2) or ''
        if t.startswith(('http:', 'https:', 'mailto:')):
            return m.group(0)
        p = os.path.normpath(os.path.join(os.path.dirname(path), t))
        return '](' + os.path.relpath(p, 'docs') + frag + ')'
    return re.sub(r'\]\(([^)#\s]+)(#[^)\s]*)?\)', fix, text)


def section_key(sec):
    return [int(x) for x in sec.split('.')] if sec else [-1]


def collect():
    rows = []
    for path in lean_files():
        for text, name, line, kind in docstrings(path):
            lead, ts = tags(text)
            for t in ts:
                for k, (spec, sec), note in parse(t, f'{path}:{line}'):
                    rows.append({'kind': k, 'spec': spec, 'sec': sec, 'note': rebase(note, path), 'path': path,
                                 'line': line, 'name': name, 'decl': kind, 'summary': summary(lead)})
    return rows


def link(r):
    href = os.path.relpath(os.path.join(ROOT, r['path']), os.path.join(ROOT, 'docs'))
    label = f'`{r["name"]}`' if r['name'] else f'{r["decl"] or "declaration"} in `{os.path.basename(r["path"])}`'
    return f'[{label}]({href}#L{r["line"]})'


def render(rows):
    out = ['# Specification ledger', '',
           'Generated by [`scripts/spec_ledger.py`](../scripts/spec_ledger.py) from the `Spec:` tags in the Lean '
           'docstrings; do not edit. The convention is in [`specification.md`](specification.md#the-specification-ledger). '
           'Per specification and section: the rules that **cite** it, the **unspecified** behaviour the models had to '
           'take from an implementation, with the evidence, and the **contradictions**, with the two sources and a witness.',
           '', '| specification | sections | cites | unspecified | contradicts |', '|---|---|---|---|---|']
    for spec in SPECS:
        rs = [r for r in rows if r['spec'] == spec]
        n = lambda k: sum(1 for r in rs if r['kind'] == k)
        out.append(f'| [{spec}](#{spec.lower()}) | {len({r["sec"] for r in rs})} | {n("cites")} | '
                   f'{n("unspecified")} | {n("contradicts")} |')
    for spec, title in SPECS.items():
        rs = [r for r in rows if r['spec'] == spec]
        out += ['', f'## {spec}', '', f'{title}.']
        open_items = [r for r in rs if r['kind'] != 'cites']
        if open_items:
            out += ['', '**Open items.**']
            for r in sorted(open_items, key=lambda r: (r['kind'], section_key(r['sec']), r['path'], r['line'])):
                sec = f'§{r["sec"]}' if r['sec'] else '(no section)'
                out.append(f'- {r["kind"]}, {sec}, {link(r)}: {r["note"]}')
        for sec in sorted({r['sec'] for r in rs}, key=section_key):
            out += ['', f'### {spec} §{sec}' if sec else f'### {spec}, no section', '']
            for r in sorted([r for r in rs if r['sec'] == sec], key=lambda r: (KINDS.index(r['kind']), r['path'], r['line'])):
                text = r['note'] if r['kind'] != 'cites' else r['summary']
                out.append(f'- **{r["kind"]}** {link(r)}' + (f': {text}' if text else ''))
    text = '\n'.join(out) + '\n'
    fixed, _ = lint_links.process(OUT, text, True)
    return fixed


def main():
    text = render(collect())
    if '--check' in sys.argv:
        old = open(os.path.join(ROOT, OUT), encoding='utf-8').read() if os.path.exists(os.path.join(ROOT, OUT)) else ''
        if old != text:
            print(f'{OUT} is out of date: run python3 -I scripts/spec_ledger.py')
            sys.exit(1)
        print(f'{OUT} is current')
        return
    open(os.path.join(ROOT, OUT), 'w', encoding='utf-8').write(text)
    print(f'wrote {OUT}')


if __name__ == '__main__':
    main()
