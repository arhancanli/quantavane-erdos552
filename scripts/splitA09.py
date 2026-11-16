#!/usr/bin/env python3
"""Split of the refined n = 51 pattern A09 (33333333; encoding-2 labels, see cubesA51.py), 12 Nov 2026.
Blocks B(57) = 49..44, ..., B(52) = 19..14 are perfect matchings (bl0-bl1, bl2-bl3, bl4-bl5, top-down order); B(51) =
13..7 and B(50) = 6..0 hold three edges and one unmatched vertex, z1 = 7 and z2 = 0. z1 (degree 8, no neighbour in
its own block) has exactly one neighbour in each of the other seven blocks: in a perfect-matching block WLOG bl0 (the
block's matching automorphisms are transitive); in B(50) a matched vertex (WLOG 6) or z2. Then z2 has one neighbour
in each of B(57..52) and B(51): in a perfect-matching block, up to the automorphisms fixing bl0 (hence bl1), it is
bl0 (type 0), bl1 (type 1) or bl2 (type 2); at most one type 0 (z1 and z2 have at most one common neighbour); in
B(51) it is z1 exactly when z1 ~ z2, otherwise WLOG 13. Orbits of the type word under the root symmetries that keep
B(51), B(50) (permute the pairs (57,56),(55,54),(53,52), swap inside a pair): lexicographic minimum. 44 sub-cubes.
Usage: splitA09.py  -> one line per sub-cube: NAME LIT ..."""
import itertools
N = 59
idx = {}
for a in range(N):
    for b in range(a + 1, N): idx[(a, b)] = len(idx) + 1
def X(a, b): return idx[(min(a, b), max(a, b))]
pm = [57, 56, 55, 54, 53, 52]
B = {}; cur = 49
for u, s in zip(pm + [51, 50], [6] * 6 + [7, 7]):
    B[u] = list(range(cur, cur - s, -1)); cur -= s
z1, z2 = B[51][6], B[50][6]
assert (z1, z2) == (7, 0)
G = []
for perm in itertools.permutations(range(3)):
    for sw in itertools.product((0, 1), repeat=3):
        p = []
        for k in range(3):
            a, b = 2 * perm[k], 2 * perm[k] + 1
            p += [b, a] if sw[k] else [a, b]
        G.append(p)
out = []
for adj in (0, 1):                      # adj = 1: z1 ~ z2
    base = [X(z1, B[u][0]) for u in pm]
    base.append(X(z1, z2) if adj else X(z1, B[50][0]))
    if not adj: base.append(-X(z1, z2))
    base.append(X(z2, z1) if adj else X(z2, B[51][0]))
    for w in itertools.product((0, 1, 2), repeat=6):
        if w.count(0) > 1: continue
        if min(tuple(w[p[k]] for k in range(6)) for p in G) != w: continue
        lits = list(base) + [X(z2, B[u][t]) for u, t in zip(pm, w)]
        out.append((f'A09s_{"adj" if adj else "non"}_' + ''.join(map(str, w)), lits))
for name, lits in out:
    print(name, ' '.join(map(str, lits)))
