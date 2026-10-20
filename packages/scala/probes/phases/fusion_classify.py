import re, subprocess, sys, os, collections
def javap(d, f):
    if not f.endswith('.class'): return None
    r = subprocess.run(['javap', '-v', '-p', '-cp', d, f[:-6]], capture_output=True, text=True)
    return [l for l in r.stdout.splitlines() if not re.match(r'\s*(Classfile|Last modified|SHA-256|MD5|Compiled from)', l)]
def norm(ls):  # drop constant pool indices
    return [re.sub(r'#\d+(\.#\d+)?', '#', l) for l in ls if not re.match(r'\s+#\d+ = ', l)]
cats = collections.Counter(); per = collections.defaultdict(list)
for line in open(sys.argv[1]):
    m = re.match(r'DIFFER (\S+): (.*) \((\S+) (\S+)\)$', line.strip())
    if not m: continue
    src, files, a, b = m.group(1), m.group(2).split(), m.group(3), m.group(4)
    kinds = set()
    for f in files:
        pa, pb = os.path.join(a, f), os.path.join(b, f)
        if not (os.path.exists(pa) and os.path.exists(pb)): kinds.add('file set'); continue
        if f.endswith('.tasty'): kinds.add('tasty'); continue
        ja, jb = javap(a, f), javap(b, f)
        if ja == jb: kinds.add('bytes only'); continue
        na, nb = norm(ja), norm(jb)
        if na == nb: kinds.add('constant pool order'); continue
        import difflib
        d = [l for l in difflib.unified_diff(na, nb, lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
        if all(re.match(r'[+-]\s+line \d+: \d+', l) for l in d): kinds.add('line numbers')
        elif all(re.match(r'[+-]\s+(ScalaInlineInfo: length|[0-9A-F]{2}( [0-9A-F]{2})*\s*$)', l) or re.match(r'[+-]\s*$', l) for l in d): kinds.add('ScalaInlineInfo only')
        else:
            sig = set()
            if any('ObjectRef' in l for l in d) and any(re.search(r'Lazy(Ref|Int|Long|Boolean|Byte|Short|Char|Float|Double|Unit)', l) for l in d): sig.add('lazy holder boxed (unfused)')
            if any(re.match(r'-.*\$\$outer\(\)', l) for l in d): sig.add('outer accessor kept (fused)')
            if any(re.match(r'-.*ACC_SYNTHETIC', l) for l in d) and any('$outer' in l for l in d): sig.add('outer field differs')
            if not sig: sig.add('other'); per['_other'].append((src, f, d[:8]))
            kinds |= sig
    k = '+'.join(sorted(kinds)); cats[k] += 1; per[k].append(src)
for k, n in cats.most_common(): print(n, k, '  e.g.', ' '.join(os.path.basename(s) for s in per[k][:4]))
for src, f, d in per['_other'][:12]: print('\n#', os.path.basename(src), f); print('\n'.join(x[:160] for x in d))
