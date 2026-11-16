#!/usr/bin/env python3
"""Encoding-1 layout for Erdős #552, n = 51, case A (some vertex in exactly 3 triangles), 12 Nov 2026; separate code
from cubesA51.py. Base: enc552.py 59 8 3 BASE 3 (root 0; N(0) = 1..8 with the matching 1-2, 3-4, 5-6, unmatched 7, 8;
blocks A(1) = 9..14, ..., A(6) = 39..44 (6 vertices), A(7) = 45..51, A(8) = 52..58 (7 vertices), upward; no far vertex;
every vertex in >= 3 triangles). Block A(u) spans c_u edges, c_u in {2,3} for u = 1..6 and c_u = 3 for u = 7, 8,
relabelled to (1st,2nd), (3rd,4th), (5th,6th) in increasing order. Orbit representatives under the 48 symmetries of
the root (explicit list: permute the pairs {1,2},{3,4},{5,6}, swap inside a pair), lexicographic minimum.
Usage: cubesA51a.py BASE OUTDIR"""
import sys, os, itertools
base, outdir = sys.argv[1], sys.argv[2]
N = 59
pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
var = {p: k + 1 for k, p in enumerate(pairs)}
def x(i, j): return var[(min(i, j), max(i, j))]
size = {u: 6 for u in range(1, 7)}; size[7] = size[8] = 7
blocks = {}; nxt = 9
for u in range(1, 9):
    blocks[u] = list(range(nxt, nxt + size[u])); nxt += size[u]
assert nxt == 59
syms = []
for perm in itertools.permutations(range(3)):
    for sw in itertools.product((0, 1), repeat=3):
        def g(c, perm=perm, sw=sw):
            o = []
            for k in range(3):
                a, b = c[2 * perm[k]], c[2 * perm[k] + 1]
                o += [b, a] if sw[k] else [a, b]
            return tuple(o)
        syms.append(g)
assert len(syms) == 48
reps = [c for c in itertools.product((2, 3), repeat=6) if min(g(c) for g in syms) == c]
os.makedirs(outdir, exist_ok=True)
head, body = open(base).read().split('\n', 1)
nv, nc = map(int, head.split()[2:4])
for k, c6 in enumerate(reps):
    c = list(c6) + [3, 3]
    units = []
    for u in range(1, 9):
        bl = blocks[u]
        want = {(bl[2 * i], bl[2 * i + 1]) for i in range(c[u - 1])}
        for a, b in itertools.combinations(bl, 2):
            units.append(x(a, b) if (a, b) in want else -x(a, b))
    with open(os.path.join(outdir, f'a{k:02d}_' + ''.join(map(str, c)) + '.cnf'), 'w') as f:
        f.write(f'p cnf {nv} {nc + len(units)}\n'); f.write(body)
        if not body.endswith('\n'): f.write('\n')
        for l in units: f.write(f'{l} 0\n')
print(len(reps), 'cubes')
