#!/usr/bin/env python3
"""Encoding-1 split of the refined n = 51 pattern a09 (33333333), separate code from splitA09.py, 12 Nov 2026.
Layout of enc552.py 59 8 3 .. 3 + cubesA51a.py: perfect-matching blocks A(1..6) = 9..44 (edges (b0,b1),(b2,b3),
(b4,b5), increasing order), A(7) = 45..51 and A(8) = 52..58 with three edges and unmatched z1 = 51, z2 = 58.
z1 has one neighbour in each of A(1..6) (WLOG b0) and in A(8) (WLOG 52, or z2); z2 has one neighbour in each of
A(1..6), of type 0/1/2 = b0/b1/b2 up to the automorphisms fixing b0 (at most one type 0), and in A(7) it is z1 iff
z1 ~ z2, else WLOG 45. Orbits of the type word under the 48 root symmetries (permute the pairs of blocks
{1,2},{3,4},{5,6}, swap inside a pair) = the multiset of unordered type pairs; first word met is kept.
Usage: splitA09a.py -> lines NAME LIT ..."""
import itertools
N = 59
pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
var = {p: k + 1 for k, p in enumerate(pairs)}
def x(i, j): return var[(min(i, j), max(i, j))]
blk = {u: list(range(9 + 6 * (u - 1), 15 + 6 * (u - 1))) for u in range(1, 7)}
A7, A8 = list(range(45, 52)), list(range(52, 59))
z1, z2 = A7[6], A8[6]
lines = []
for adj in (0, 1):
    seen = set()
    for w in itertools.product((0, 1, 2), repeat=6):
        if sum(1 for t in w if t == 0) > 1: continue
        key = tuple(sorted(tuple(sorted(w[2 * k:2 * k + 2])) for k in range(3)))
        if key in seen: continue
        seen.add(key)
        lits = [x(z1, blk[u][0]) for u in range(1, 7)]
        if adj: lits += [x(z1, z2), x(z2, z1)]
        else: lits += [x(z1, A8[0]), -x(z1, z2), x(z2, A7[0])]
        lits += [x(z2, blk[u][t]) for u, t in zip(range(1, 7), w)]
        lines.append(('a09s_' + ('adj' if adj else 'non') + '_' + ''.join(map(str, w)), lits))
for name, lits in lines:
    print(name, ' '.join(map(str, lits)))
