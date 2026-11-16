#!/usr/bin/env python3
"""A C4-free graph on 58 vertices with minimum degree 7 (so R(C4, K_{1,51}) > 58), 12 Nov 2026.
ER_8 = polarity graph of PG(2,8) (x ~ y iff x.y = 0, x != y; GF(8) = GF(2)[t]/(t^3+t+1)). Its absolute points form
the line l: x1+x2+x3 = 0, with pole p = (1,1,1). Delete l and p: 63 vertices, every degree 8 (each other point x has
exactly one neighbour on l, the point x^perp meet l). Then delete 5 of the 7 points of a line L through p other than
p and L meet l: two such points span L, whose pole lies on l (L passes through p), so they have no common neighbour
left, and every remaining vertex loses at most one neighbour: degree >= 7. Writes the edge list ("n m" + edges)."""
import itertools, sys
def mul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
def inv(a):
    return next(b for b in range(1, 8) if mul(a, b) == 1)
def norm(v):
    for c in v:
        if c:
            ic = inv(c); return tuple(mul(ic, x) for x in v)
pts = sorted({norm(v) for v in itertools.product(range(8), repeat=3) if any(v)})
assert len(pts) == 73
dot = lambda x, y: mul(x[0], y[0]) ^ mul(x[1], y[1]) ^ mul(x[2], y[2])
absolute = [x for x in pts if dot(x, x) == 0]
assert all(x[0] ^ x[1] ^ x[2] == 0 for x in absolute) and len(absolute) == 9
p = (1, 1, 1)
r = next(x for x in pts if x != p and x[0] ^ x[1] ^ x[2] != 0)
L = sorted({norm(tuple(a ^ mul(t, b) for a, b in zip(r, p))) for t in range(8)} | {p})
assert len(L) == 9 and p in L
onl = [x for x in L if x in absolute]
cand = [x for x in L if x != p and x not in absolute]
assert len(onl) == 1 and len(cand) == 7
S = set(absolute) | {p} | set(cand[:5])
V = [x for x in pts if x not in S]
assert len(V) == 58
lab = {x: i for i, x in enumerate(V)}
E = [(lab[x], lab[y]) for x, y in itertools.combinations(V, 2) if dot(x, y) == 0]
out = sys.argv[1]
with open(out, 'w') as f:
    f.write(f'{len(V)} {len(E)}\n')
    for a, b in E: f.write(f'{a} {b}\n')
print('vertices', len(V), 'edges', len(E))
