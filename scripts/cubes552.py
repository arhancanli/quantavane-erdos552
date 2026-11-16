#!/usr/bin/env python3
# Case split of case e = 3 (every vertex in exactly 3 triangles) on the neighbourhood of the far vertex 44.
# Layout of enc552.py (N=46, DEG=7, E=3, BLK): A(1)=8..12, A(2)=13..17, A(3)=18..22, A(4)=23..27,
# A(5)=28..32, A(6)=33..37 (last vertex of each = the M-partner of u), A(7)=38..43; far = {44, 45}.
# 44 is adjacent to no vertex of {0..7}, to at most one vertex per block (C4), so either to 45 and to one
# vertex in each of 6 blocks, or to one vertex in each of the 7 blocks. Inside a block the symmetry group
# fixing the BLK layout lets us take the neighbour to be the first edge-vertex ('e') or the M-partner ('m').
# The symmetry of vertex 0 (permute the triangle pairs (1,2),(3,4),(5,6), swap inside a pair) lets us
# keep one pattern per orbit.  Usage: cubes552.py BASE.cnf OUTDIR
import sys, itertools, os
base, outdir = sys.argv[1], sys.argv[2]
N = 46
pairs = [(i, j) for i in range(N) for j in range(i+1, N)]
var = {p: k+1 for k, p in enumerate(pairs)}
def x(i, j): return var[(min(i, j), max(i, j))]
blocks = {1: list(range(8, 13)), 2: list(range(13, 18)), 3: list(range(18, 23)), 4: list(range(23, 28)),
          5: list(range(28, 33)), 6: list(range(33, 38)), 7: list(range(38, 44))}
def canon(t):  # t = types of blocks 1..6
    prs = [tuple(sorted(t[0:2])), tuple(sorted(t[2:4])), tuple(sorted(t[4:6]))]
    return tuple(sorted(prs))
seen = {}
for adj45 in (0, 1):
    for t in itertools.product('nem', repeat=6):
        for t7 in ('n', 'e'):
            types = list(t) + [t7]
            nn = types.count('n')
            if adj45 == 0 and nn != 0: continue
            if adj45 == 1 and nn != 1: continue
            key = (adj45, canon(t), t7)
            if key in seen: continue
            seen[key] = (adj45, types)
os.makedirs(outdir, exist_ok=True)
hdr = open(base).readline().split()
nv, nc = int(hdr[2]), int(hdr[3])
body = open(base).read().split('\n', 1)[1]
names = []
for k, (adj45, types) in enumerate(sorted(seen.values())):
    units = [x(44, 45) if adj45 else -x(44, 45)]
    for u in range(1, 8):
        bl = blocks[u]; ty = types[u-1]
        if ty == 'n':
            units += [-x(44, w) for w in bl]
        elif ty == 'e':
            units.append(x(44, bl[0]))
        else:
            units.append(x(44, bl[-1]))
    name = f'cube{k:03d}_{adj45}_{"".join(types)}'
    with open(os.path.join(outdir, name + '.cnf'), 'w') as f:
        f.write(f'p cnf {nv} {nc + len(units)}\n')
        f.write(body)
        if not body.endswith('\n'): f.write('\n')
        for l in units: f.write(f'{l} 0\n')
    names.append(name)
print(len(names), 'cubes')
