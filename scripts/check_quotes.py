"""Checks the specification quotes in the literate pages against the specifications.

A quote is a Verso block quote (`>` lines) followed by an attribution line that links to the
section it quotes, for example

    — [JVMS §5.4.3.2](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.3.2), Java SE 21.

For each quote the script fetches the linked page once (cached in `.cache/specs/`), takes the text
of the anchored section up to the next section heading, and fails unless every paragraph of the
quote appears in it verbatim, up to whitespace. It also reports how much is quoted from each
Oracle specification: their licence allows brief excerpts that do not, in aggregate, make up a
significant portion of the specification, so the total is kept under a budget.

Usage: python3 -I scripts/check_quotes.py
"""
import glob
import html
import os
import re
import sys
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.path.join(ROOT, '.cache', 'specs')
ATTRIB = re.compile(r'^— \[([^\]]+)\]\((https?://[^)#]+)#([^)]+)\)')
# Words quoted, in total, per Oracle specification: a few hundred words of a 300-page book.
BUDGET = {'docs.oracle.com/javase/specs/jvms': 1500, 'docs.oracle.com/javase/specs/jls': 1500}


def fetch(url):
    os.makedirs(CACHE, exist_ok=True)
    path = os.path.join(CACHE, re.sub(r'[^A-Za-z0-9.]+', '_', url))
    if not os.path.exists(path):
        with urllib.request.urlopen(url) as r:
            open(path, 'wb').write(r.read())
    return open(path, encoding='utf-8', errors='replace').read()


def norm(s):
    s = re.sub(r'<[^>]+>', '', s)
    s = html.unescape(s)
    return re.sub(r'\s+', ' ', s).strip()


def section_text(page, anchor):
    """The text from the element with id or name `anchor` to the next section of the same depth."""
    m = re.search(r'(?:id|name)="' + re.escape(anchor) + r'"', page)
    if not m:
        return None
    start = m.start()
    depth = anchor.count('.')
    nxt = re.compile(r'(?:id|name)="(jvms|jls)-[0-9.]+"')
    end = len(page)
    for n in nxt.finditer(page, m.end()):
        a = n.group(0).split('"')[1]
        if a.count('.') <= depth:
            end = n.start()
            break
    return norm(page[start:end])


def quotes(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    i = 0
    while i < len(lines):
        if lines[i].startswith('>'):
            j = i
            block = []
            while j < len(lines) and lines[j].startswith('>'):
                block.append(lines[j][1:].strip())
                j += 1
            k = j
            while k < len(lines) and not lines[k].strip():
                k += 1
            m = ATTRIB.match(lines[k]) if k < len(lines) else None
            paras = [norm(p) for p in '\n'.join(block).split('\n\n') if p.strip()]
            yield i + 1, paras, m
            i = j
        else:
            i += 1


def main():
    problems, words = [], {}
    files = sorted(glob.glob(os.path.join(ROOT, 'literate', '**', '*.lean'), recursive=True))
    files = [f for f in files if '/.lake/' not in f]
    n = 0
    for f in files:
        rel = os.path.relpath(f, ROOT)
        for line, paras, m in quotes(f):
            n += 1
            if not m:
                problems.append(f'{rel}:{line}: a quote without an attribution line linking to its section')
                continue
            label, url, anchor = m.groups()
            text = section_text(fetch(url), anchor)
            if text is None:
                problems.append(f'{rel}:{line}: no section #{anchor} at {url}')
                continue
            for p in paras:
                if p not in text:
                    problems.append(f'{rel}:{line}: not verbatim in {label}: "{p[:70]}…"')
            for k in BUDGET:
                if k in url:
                    words[k] = words.get(k, 0) + sum(len(p.split()) for p in paras)
    for k, w in words.items():
        print(f'{k}: {w} words quoted (budget {BUDGET[k]})')
        if w > BUDGET[k]:
            problems.append(f'{k}: {w} words quoted, over the budget of {BUDGET[k]}')
    print('\n'.join(problems) if problems else f'{n} quotes verbatim')
    sys.exit(1 if problems else 0)


if __name__ == '__main__':
    main()
