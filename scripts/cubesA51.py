#!/usr/bin/env python3
"""Erdős #552, n = 51, case A split (encoding 2 layout), 12 Nov 2026. Base: NV=59 DV=8 TRIEDGES=6 enc552b.py 3 1 BASE
(root 58 in exactly 3 triangles; N(root) = 57..50 with the matching 57-56, 55-54, 53-52 and unmatched 51, 50; blocks
B(57) = 49..44, B(56) = 43..38, B(55) = 37..32, B(54) = 31..26, B(53) = 25..20, B(52) = 19..14 (6 vertices),
B(51) = 13..7, B(50) = 6..0 (7 vertices); no far vertex). Every vertex lies in 3 or 4 triangles, so for u in N(root)
the block B(u) spans c_u edges (a matching) with c_u in {2, 3} (u matched: e(u) = 1 + c_u) or c_u = 3 (u unmatched:
e(u) = c_u, at most 3 in 7 vertices). Relabel each block so its edges are the consecutive pairs (top-down order).
Patterns (c_57..c_52) up to the root's symmetries (permute the three pairs, swap inside a pair): the multiset of
unordered pairs {c_a, c_b}: 10 cubes.   Usage: cubesA51.py BASE OUTDIR"""
import sys, os, itertools
base, outdir = sys.argv[1], sys.argv[2]
N = 59
idx = {}
for a in range(N):
    for b in range(a + 1, N): idx[(a, b)] = len(idx) + 1
def X(a, b): return idx[(min(a, b), max(a, b))]
nbr = [57, 56, 55, 54, 53, 52, 51, 50]
sizes = [6, 6, 6, 6, 6, 6, 7, 7]
B = {}; cur = 49
for u, s in zip(nbr, sizes):
    B[u] = list(range(cur, cur - s, -1)); cur -= s
assert cur == -1
reps = {}
for c in itertools.product((2, 3), repeat=6):
    key = tuple(sorted(tuple(sorted(c[2 * k:2 * k + 2])) for k in range(3)))
    if key not in reps: reps[key] = c
os.makedirs(outdir, exist_ok=True)
head, body = open(base).read().split('\n', 1)
nv, nc = map(int, head.split()[2:4])
for k, key in enumerate(sorted(reps)):
    c = list(reps[key]) + [3, 3]
    units = []
    for u, cu in zip(nbr, c):
        bl = B[u]
        want = {tuple(sorted((bl[2 * i], bl[2 * i + 1]))) for i in range(cu)}
        for a, b in itertools.combinations(sorted(bl), 2):
            units.append(X(a, b) if (a, b) in want else -X(a, b))
    name = f'A{k:02d}_' + ''.join(map(str, c))
    with open(os.path.join(outdir, name + '.cnf'), 'w') as f:
        f.write(f'p cnf {nv} {nc + len(units)}\n'); f.write(body)
        if not body.endswith('\n'): f.write('\n')
        for l in units: f.write(f'{l} 0\n')
print(len(reps), 'cubes')
