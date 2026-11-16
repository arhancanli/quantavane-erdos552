#!/usr/bin/env python3
"""Erdős #552, n = 51, case A, the last pattern 33333333 (cubesA51.py: A09), 12 Nov 2026.
Derived constraint (README.md, n = 51, step 4): the nine patterns with some c_u = 2 (A00-A08) are UNSAT, and the formula
family is closed under relabelling, so no vertex with exactly 3 triangles has a triangle-neighbour with exactly 3
triangles. In A09 the unmatched neighbours 51 and 50 of the root lie in exactly 3 triangles (their 7-vertex blocks
hold at most 3 edges); hence every matched vertex of B(51) = 13..8 and B(50) = 6..1 (the vertices in triangles with
51 resp. 50) lies in 4 triangles, i.e. each of its 8 edges lies in a triangle. Encoded with fresh variables
t(y,w,x) -> y~x, w~x and clauses  not y~w  or  OR_x t(y,w,x).
The base encoder is re-run (runpy, output to /dev/null) to know which pairs it fixed.
Usage: NV=59 DV=8 TRIEDGES=6 refineA51.py IN.cnf OUT.cnf"""
import sys, runpy
inp, outp = sys.argv[1], sys.argv[2]
sys.argv = ['enc552b.py', '3', '1', '/dev/null']
ns = runpy.run_path(__file__.replace('refineA51.py', 'enc552b.py'), run_name='__main__')
N, F, idx = ns['N'], ns['F'], ns['idx']
head, body = open(inp).read().split('\n', 1)
nv, nc = map(int, head.split()[2:4])
top = [nv]
def fresh():
    top[0] += 1; return top[0]
def L(a, b):
    p = (min(a, b), max(a, b))
    if p in F: return F[p]
    return idx[p]
extra = []
targets = list(range(13, 7, -1)) + list(range(6, 0, -1))
for y in targets:
    for w in range(N):
        if w == y: continue
        e = L(y, w)
        if e is False: continue
        ts = []
        for x in range(N):
            if x in (y, w): continue
            a, b = L(y, x), L(w, x)
            if a is False or b is False: continue
            t = fresh(); ts.append(t)
            if a is not True: extra.append([-t, a])
            if b is not True: extra.append([-t, b])
        c = ([] if e is True else [-e]) + ts
        if not c: raise SystemExit('contradiction')
        extra.append(c)
with open(outp, 'w') as f:
    f.write(f'p cnf {top[0]} {nc + len(extra)}\n'); f.write(body)
    if not body.endswith('\n'): f.write('\n')
    for c in extra: f.write(' '.join(map(str, c)) + ' 0\n')
print('refined: vertices', targets, 'new vars', top[0] - nv, 'new clauses', len(extra))
