#!/usr/bin/env python3
# ci/frame_lint.py - the machine's invariant that C cannot check: a step never stores into its frame across a nested run.
#
# Frames live on one growable stack (machine.h); F is re-derived from the frame's offset at every use because a push
# may move the stack. A statement  F->x = f(...)  where f runs the machine (reaches mrun, directly or through what it
# calls) lets the compiler take &F->x before the call: the nested run may grow the stack, and the store lands in the
# freed buffer. Such a store must compute into a local first:  { T v = f(...); F->x = v; }
# This lists every step function's store into its frame whose right side calls a function that may run the machine
# (found by a call graph over the given files, keyed per file), and every store of a call through a function pointer
# (which the call graph cannot follow). Exit status 1 if there is any. Usage: frame_lint.py FILE.c...
import re, sys

files = sys.argv[1:]
defs, byname, src = {}, {}, {}
for f in files:
    s = open(f).read(); src[f] = s
    s2 = re.sub(r'/\*.*?\*/', '', s, flags=re.S); s2 = re.sub(r'"(\\.|[^"\\])*"', '""', s2)
    for m in re.finditer(r'^[A-Za-z_][\w\s\*]*?\b(\w+)\s*\(([^;{)]*)\)\s*\{', s2, re.M):
        name = m.group(1)
        if name in ('if', 'while', 'for', 'switch', 'return'): continue
        i, d = m.end(), 1
        while d and i < len(s2):
            d += {'{': 1, '}': -1}.get(s2[i], 0); i += 1
        defs[(f, name)] = s2[m.end():i]; byname.setdefault(name, []).append(f)

def resolve(f, c):
    if (f, c) in defs: return (f, c)
    fs = byname.get(c)
    return (fs[0], c) if fs and len(fs) == 1 else None

calls = {k: {r for r in (resolve(k[0], c) for c in re.findall(r'\b(\w+)\s*\(', b)) if r} for k, b in defs.items()}
runs = {k for k, b in defs.items() if re.search(r'\bmrun\s*\(', b)}
changed = True
while changed:
    changed = False
    for k, cs in calls.items():
        if k not in runs and cs & runs: runs.add(k); changed = True

found = 0
for f in files:
    cur = None
    for i, l in enumerate(src[f].split('\n'), 1):
        m = re.match(r'^static void (\w+)\(size_t off\) \{', l)
        if m: cur = m.group(1); continue
        if l.startswith('}'): cur = None
        if not cur: continue
        for m in re.finditer(r'(?<![\w>*])F->(\w+)(\[[^\]]*\])?\s*=(?!=)([^;]*);', l):
            rhs = m.group(3)
            bad = [c for c in re.findall(r'\b(\w+)\s*\(', rhs) if resolve(f, c) in runs]
            if re.search(r'\bF->\w+\s*\(', rhs): bad.append('a call through a function pointer')
            if bad:
                found += 1
                print(f"{f}:{i}: {cur}: F->{m.group(1)}{m.group(2) or ''} = ... {', '.join(bad)} (compute into a local, then store)")
sys.exit(1 if found else 0)
