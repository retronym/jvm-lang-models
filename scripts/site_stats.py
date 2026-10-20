"""Fills the site's home page with the model's sizes from `docs/stats.md`.

`site/index.html` carries a JSON block (`<script type="application/json" id="stats">`) with each
package's theorems, checked examples and lines, the totals and the number of programs probed on
HotSpot, and `data-stat` elements that show the totals. This rewrites both from `docs/stats.md`,
so the page cannot drift from the generated counts. The Pages workflow runs it when it assembles
the site; run it in place after regenerating `docs/stats.md` to keep the committed copy current.

Usage: python3 -I scripts/site_stats.py [IN [OUT]]   (default: site/index.html, in place)
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATS = os.path.join(ROOT, 'docs', 'stats.md')
ROW = re.compile(r'^\| \[`([^`]+)`\]\([^)]*\) \| ([\d,]+) \| ([\d,]+) \| ([\d,]+) \| ([\d,]+) \|$', re.M)
TOTAL = re.compile(r'^\| \*\*total\*\* \| \*\*([\d,]+)\*\* \| \*\*([\d,]+)\*\* \| \*\*([\d,]+)\*\* \| \*\*([\d,]+)\*\* \|$', re.M)
PROBED = re.compile(r'^\| \*\*probed\*\* \| \| \*\*([\d,]+)\*\* \|$', re.M)
BLOCK = re.compile(r'(<script type="application/json" id="stats">\n).*?(\n</script>)', re.S)


def num(s):
    return int(s.replace(',', ''))


def stats():
    text = open(STATS, encoding='utf-8').read()
    packages = {m[1]: {'files': num(m[2]), 'lines': num(m[3]), 'theorems': num(m[4]), 'examples': num(m[5])}
                for m in ROW.finditer(text)}
    total, probed = TOTAL.search(text), PROBED.search(text)
    if not packages or not total or not probed:
        sys.exit(f'{STATS}: the package table, its total or the probed total is missing')
    return {'packages': packages,
            'total': {'files': num(total[1]), 'lines': num(total[2]), 'theorems': num(total[3]),
                      'examples': num(total[4]), 'probed': num(probed[1])}}


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'site', 'index.html')
    out = sys.argv[2] if len(sys.argv) > 2 else src
    page = open(src, encoding='utf-8').read()
    s = stats()
    if not BLOCK.search(page):
        sys.exit(f'{src}: no stats block')
    page = BLOCK.sub(lambda m: m[1] + json.dumps(s, indent=1, sort_keys=True) + m[2], page)
    for key, value in s['total'].items():
        page = re.sub(rf'(<b data-stat="{key}">)[^<]*(</b>)', lambda m: f'{m[1]}{value:,}{m[2]}', page)
    with open(out, 'w', encoding='utf-8') as f:
        f.write(page)


if __name__ == '__main__':
    main()
