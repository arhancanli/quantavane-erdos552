#!/usr/bin/env python3
# Control: find a C4-free graph on 46 vertices with minimum degree >= 6 (consistent with the published
# R(C4, K_{1,40}) = 47): take the Erdos-Renyi polarity graph ER_7 of PG(2,7) (57 vertices, C4-free; degrees
# 7 and 8) and delete 11 vertices so that every remaining vertex keeps degree >= 6 (random local search).
import itertools, random, sys
q = 7
pts = []
for v in itertools.product(range(q), repeat=3):
    if v == (0, 0, 0): continue
    # normalise: first nonzero coordinate = 1
    f = next(c for c in v if c)
    inv = pow(f, q-2, q)
    w = tuple((c*inv) % q for c in v)
    if w not in pts: pts.append(w)
assert len(pts) == q*q+q+1
n = len(pts)
adj = [set() for _ in range(n)]
for i in range(n):
    for j in range(i+1, n):
        if sum(a*b for a, b in zip(pts[i], pts[j])) % q == 0:
            adj[i].add(j); adj[j].add(i)
deg = [len(a) for a in adj]
print('ER_7: n', n, 'degree counts', {d: deg.count(d) for d in set(deg)}, file=sys.stderr)
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
K, NEED = n - 46, 6
def bad(D):
    Ds = set(D)
    return sum(max(0, NEED - len(adj[v] - Ds)) for v in range(n) if v not in Ds)
best = None
for restart in range(2000):
    D = rng.sample(range(n), K)
    cur = bad(D)
    for it in range(4000):
        if cur == 0: break
        i = rng.randrange(K); v = rng.choice([u for u in range(n) if u not in D])
        D2 = D[:]; D2[i] = v
        c2 = bad(D2)
        if c2 <= cur or rng.random() < 0.02:
            D, cur = D2, c2
    if cur == 0:
        best = D; break
if best is None:
    print('NOT FOUND'); sys.exit(1)
keep = [v for v in range(n) if v not in set(best)]
lab = {v: k for k, v in enumerate(keep)}
edges = sorted((lab[i], lab[j]) for i in keep for j in adj[i] if j in lab and i < j)
print(len(keep), len(edges))
for a, b in edges: print(a, b)
