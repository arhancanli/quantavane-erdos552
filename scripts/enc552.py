#!/usr/bin/env python3
# Erdos #552, n = 39: is there a C4-free graph on 46 vertices with minimum degree >= 7?
# Counting (README.md, Lemma 1) shows such a graph is 7-regular and every neighbourhood spans 2 or 3 disjoint edges.
# Case e in {2,3}: vertex 0 has N(0) = {1..7}, the e edges in N(0) are 1-2, 3-4 (, 5-6);
# the private second neighbourhoods A(u) are consecutive blocks of 8..45 (sizes 6 - m(u));
# for e = 3 the two vertices 44, 45 are at distance >= 3 from 0.
# Usage: enc552.py N DEG E out.cnf        (N=46, DEG=7, E=2 or 3); E=0 means no symmetry breaking.
import sys, itertools
N, DEG, E = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); out = sys.argv[4]
pairs = [(i, j) for i in range(N) for j in range(i+1, N)]
var = {p: k+1 for k, p in enumerate(pairs)}
nv = [len(pairs)]
def x(i, j):
    return var[(i, j)] if i < j else var[(j, i)]
fixed = {}   # pair -> True/False
if E >= 0:
    nb0 = list(range(1, DEG+1))
    for j in range(1, N):
        fixed[(0, j)] = (j in nb0)
    matched = {}
    for t in range(E):
        a, b = 1+2*t, 2+2*t
        matched[a] = b; matched[b] = a
    for a, b in itertools.combinations(nb0, 2):
        fixed[(a, b)] = (matched.get(a) == b)
    nxt = DEG+1
    blocks = {}
    for u in nb0:
        size = DEG-1-(1 if u in matched else 0)
        blocks[u] = list(range(nxt, nxt+size)); nxt += size
    far = list(range(nxt, N))
    assert len(far) == N-1-DEG-DEG*(DEG-1)+2*E, (nxt, far)
    for u in nb0:
        for w in range(DEG+1, N):
            fixed[(u, w)] = (w in blocks[u])
    BLK = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    if BLK:
        # Case e = 3 for EVERY vertex (sound only after case e = 2 is refuted for all vertices):
        # the triangles at u in N(0) other than {0,u,p(u)} are edges inside A(u); exactly
        # DEG - 1 - |N(0) edges at u| ... i.e. 2 edges for matched u, 3 edges for the unmatched u.
        # WLOG (relabel inside each block) they are consecutive pairs.
        for u in nb0:
            bl = blocks[u]
            k = 2 if u in matched else 3
            want = set((bl[2*i], bl[2*i+1]) for i in range(k))
            for a, b in itertools.combinations(bl, 2):
                fixed[(a, b)] = ((a, b) in want)
cl = []
def lit(i, j, pos=True):
    p = (i, j) if i < j else (j, i)
    if p in fixed:
        val = fixed[p] if pos else (not fixed[p])
        return True if val else False
    return x(i, j) if pos else -x(i, j)
def add(lits):
    out_ = []
    for l in lits:
        if l is True: return
        if l is False: continue
        out_.append(l)
    if not out_:
        raise SystemExit('fixed part violates a clause: ' + repr(lits))
    cl.append(out_)
for p, v in fixed.items():
    pass  # fixed pairs are substituted, not given variables in clauses
for a, b, c, d in itertools.combinations(range(N), 4):
    for (p, q, r, s) in ((a, b, c, d), (a, b, d, c), (a, c, b, d)):
        add([lit(p, q, False), lit(q, r, False), lit(r, s, False), lit(s, p, False)])
def atmost(lits, k):
    # Sinz sequential counter: at most k of lits true
    n = len(lits)
    if k >= n: return
    if k < 0: raise SystemExit('infeasible degree')
    if k == 0:
        for l in lits: cl.append([-l])
        return
    s = [[0]*k for _ in range(n)]
    for i in range(n):
        for j in range(k):
            nv[0] += 1; s[i][j] = nv[0]
    cl.append([-lits[0], s[0][0]])
    for j in range(1, k): cl.append([-s[0][j]])
    for i in range(1, n):
        cl.append([-lits[i], s[i][0]])
        cl.append([-s[i-1][0], s[i][0]])
        for j in range(1, k):
            cl.append([-lits[i], -s[i-1][j-1], s[i][j]])
            cl.append([-s[i-1][j], s[i][j]])
        cl.append([-lits[i], -s[i-1][k-1]])
for v in range(N):
    free, cnt = [], 0
    for u in range(N):
        if u == v: continue
        l = lit(u, v)
        if l is True: cnt += 1
        elif l is False: continue
        else: free.append(l)
    need = DEG - cnt
    atmost(free, need)
    atmost([-l for l in free], len(free) - need)
TRI = int(sys.argv[5]) if len(sys.argv) > 5 else 0
if TRI:
    # every vertex lies in at least TRI triangles (y_vab -> e_va, e_vb, e_ab; at least TRI of the y_v.. true)
    for v in range(N):
        ys = []
        for a, b in itertools.combinations([u for u in range(N) if u != v], 2):
            ls = [lit(v, a), lit(v, b), lit(a, b)]
            if any(l is False for l in ls): continue
            nv[0] += 1; y = nv[0]; ys.append(y)
            for l in ls:
                if l is not True: cl.append([-y, l])
        # at least TRI of ys: r[i][j] = 'at least j of ys[0..i-1]'; require r[n][TRI]
        n_ = len(ys); k = TRI
        if n_ < k: raise SystemExit('too few triangle candidates')
        r = [[None]*(k+1) for _ in range(n_+1)]
        for i in range(1, n_+1):
            for j in range(1, k+1):
                if j > i: continue
                nv[0] += 1; r[i][j] = nv[0]
                c1 = [-r[i][j], ys[i-1]]
                if r[i-1][j] is not None: c1.append(r[i-1][j])
                cl.append(c1)
                if j > 1:
                    c2 = [-r[i][j], r[i-1][j-1]]
                    if r[i-1][j] is not None: c2.append(r[i-1][j])
                    cl.append(c2)
        cl.append([r[n_][k]])
with open(out, 'w') as f:
    f.write(f"p cnf {nv[0]} {len(cl)}\n")
    for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
print(N, DEG, E, 'vars', nv[0], 'clauses', len(cl), 'free edge vars', len(pairs) - len(fixed))
