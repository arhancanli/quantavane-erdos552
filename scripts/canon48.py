#!/usr/bin/env python3
"""Full-size green control for the lane's two encoders (12 Nov 2026). Takes a 7-regular C4-free graph on 48 vertices
in which every vertex lies in exactly 3 triangles (the Afzaly-McKay graph, controls/w48_afzaly_mckay_edges.txt),
relabels it into the fixed layout of enc552b.py (NV=48, E=3, BLK=1; layout 'b') or of enc552.py (48 7 3 .. 3 1;
layout 'a') with a chosen root, asserts every adjacency those encoders fix (root, its neighbourhood and matching,
the blocks A(u), the block-internal matchings, the far vertices), and writes one unit clause per edge variable
(pair (i,j), i<j, numbered as in both encoders). Appending the units to the encoder's CNF must give a satisfiable
formula: the encoder accepts this graph.
Usage: canon48.py EDGES LAYOUT ROOT OUT_UNITS"""
import sys, itertools

edges_file, layout, root, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
L = open(edges_file).read().split('\n')
N, M = map(int, L[0].split())
assert N == 48
adj = [set() for _ in range(N)]
for l in L[1:]:
    if l.strip():
        a, b = map(int, l.split()); adj[a].add(b); adj[b].add(a)
assert all(len(s) == 7 for s in adj)
v = root
Nv = sorted(adj[v])
inner = [(a, b) for a, b in itertools.combinations(Nv, 2) if b in adj[a]]
assert len(inner) == 3, 'root must lie in exactly 3 triangles'
matched = [x for e in inner for x in e]
[m] = [x for x in Nv if x not in matched]
A = {}
for u in Nv:
    A[u] = sorted(adj[u] - {v} - set(Nv))
covered = set().union(*A.values())
far = sorted(set(range(N)) - {v} - set(Nv) - covered)
assert len(far) == 4 and sum(len(x) for x in A.values()) == 36 and len(covered) == 36
def block_order(u, layout_kind):
    """vertices of A(u) ordered as the encoder's canonical block: the internal matching on consecutive pairs"""
    S = A[u]
    es = [(a, b) for a, b in itertools.combinations(S, 2) if b in adj[a]]
    cov = [x for e in es for x in e]
    rest = [x for x in S if x not in cov]
    if u == m:
        assert len(es) == 3 and not rest
        return [x for e in es for x in e]
    assert len(es) == 2 and len(rest) == 1
    if layout_kind == 'b':      # enc552b: bl[0] unmatched, then (bl1,bl2), (bl3,bl4)
        return rest + [x for e in es for x in e]
    return [x for e in es for x in e] + rest   # enc552: (bl0,bl1), (bl2,bl3), bl4 unmatched
perm = {}
order_nbr = [inner[0][0], inner[0][1], inner[1][0], inner[1][1], inner[2][0], inner[2][1], m]
if layout == 'b':
    perm[v] = 47
    labels = [46, 45, 44, 43, 42, 41, 40]
    cur = 39
    for u, lab in zip(order_nbr, labels):
        perm[u] = lab
        bl = block_order(u, 'b')
        for x in bl:
            perm[x] = cur; cur -= 1
    for x, lab in zip(far, [3, 2, 1, 0]):
        perm[x] = lab
    assert cur == 3
else:
    perm[v] = 0
    labels = [1, 2, 3, 4, 5, 6, 7]
    cur = 8
    for u, lab in zip(order_nbr, labels):
        perm[u] = lab
        for x in block_order(u, 'a'):
            perm[x] = cur; cur += 1
    for x, lab in zip(far, [44, 45, 46, 47]):
        perm[x] = lab
    assert cur == 44
assert sorted(perm.values()) == list(range(N))
E = {tuple(sorted((perm[a], perm[b]))) for a in range(N) for b in adj[a]}
# assert the adjacencies the encoders fix
R = 47 if layout == 'b' else 0
nb = labels
pairs = [(nb[0], nb[1]), (nb[2], nb[3]), (nb[4], nb[5])]
def has(a, b): return tuple(sorted((a, b))) in E
for x in range(N):
    if x != R: assert has(R, x) == (x in nb)
for a, b in itertools.combinations(nb, 2):
    assert has(a, b) == ((a, b) in pairs or (b, a) in pairs)
if layout == 'b':
    B = {}; cur = 39
    for u in nb:
        sz = 6 if u == 40 else 5
        B[u] = list(range(cur, cur - sz, -1)); cur -= sz
    for u in nb:
        for w in range(0, 40):
            assert has(u, w) == (w in B[u])
        bl = B[u]
        want = {(bl[0], bl[1]), (bl[2], bl[3]), (bl[4], bl[5])} if u == 40 else {(bl[1], bl[2]), (bl[3], bl[4])}
        want = {tuple(sorted(p)) for p in want}
        for a, b in itertools.combinations(bl, 2):
            assert has(a, b) == (tuple(sorted((a, b))) in want)
else:
    B = {}; cur = 8
    for u in nb:
        sz = 6 if u == 7 else 5
        B[u] = list(range(cur, cur + sz)); cur += sz
    for u in nb:
        for w in range(8, 48):
            assert has(u, w) == (w in B[u])
        bl = B[u]; k = 3 if u == 7 else 2
        want = {(bl[2 * i], bl[2 * i + 1]) for i in range(k)}
        for a, b in itertools.combinations(bl, 2):
            assert has(a, b) == ((a, b) in want)
idx = {}
for a in range(N):
    for b in range(a + 1, N):
        idx[(a, b)] = len(idx) + 1
with open(out, 'w') as f:
    for (a, b), x in idx.items():
        f.write(f"{x if (a, b) in E else -x} 0\n")
with open(out + '.edges', 'w') as f:
    f.write(f'{N} {len(E)}\n')
    for a, b in sorted(E): f.write(f'{a} {b}\n')
print(f'layout {layout} root {v}: all fixed adjacencies of the encoder hold; {len(idx)} unit clauses written; far {far}')
