#!/usr/bin/env python3
"""Encoding-1 version of refineA51.py (separate code), 12 Nov 2026. Pattern a09_33333333 of cubesA51a.py (layout of
enc552.py 59 8 3 BASE 3: root 0; unmatched neighbours 7 and 8 with blocks A(7) = 45..51, A(8) = 52..58; c = 3, so the
matched vertices are 45..50 and 52..57 and the unmatched ones 51 and 58). Same derived constraint: 7 and 8 lie in
exactly 3 triangles, so every vertex in a triangle with them (45..50, 52..57) lies in 4 triangles: each of its edges
y-w has a common neighbour x. Fresh variables s(y,w,x) -> y~x and w~x; clause  not y~w  or  OR_x s(y,w,x).
The base encoder is re-run via runpy (output to /dev/null) to learn its fixed pairs.
Usage: refineA51a.py IN.cnf OUT.cnf"""
import sys, runpy
inp, outp = sys.argv[1], sys.argv[2]
sys.argv = ['enc552.py', '59', '8', '3', '/dev/null', '3']
ns = runpy.run_path(__file__.replace('refineA51a.py', 'enc552.py'), run_name='__main__')
N, fixed, var = ns['N'], ns['fixed'], ns['var']
head, body = open(inp).read().split('\n', 1)
nv, nc = map(int, head.split()[2:4])
top = nv
def edge(a, b):
    p = (a, b) if a < b else (b, a)
    return fixed[p] if p in fixed else var[p]
cls = []
for y in list(range(45, 51)) + list(range(52, 58)):
    for w in range(N):
        if w == y: continue
        e = edge(y, w)
        if e is False: continue
        alts = []
        for x in range(N):
            if x == y or x == w: continue
            a, b = edge(y, x), edge(w, x)
            if a is False or b is False: continue
            top += 1; s = top; alts.append(s)
            for l in (a, b):
                if l is not True: cls.append([-s, l])
        c = ([] if e is True else [-e]) + alts
        assert c, 'contradiction'
        cls.append(c)
with open(outp, 'w') as f:
    f.write(f'p cnf {top} {nc + len(cls)}\n'); f.write(body)
    if not body.endswith('\n'): f.write('\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
print('refined (encoding 1): new vars', top - nv, 'new clauses', len(cls))
