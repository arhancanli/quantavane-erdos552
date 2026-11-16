#!/usr/bin/env python3
# Second, independently written encoding for Erdos #552, n = 39.
# Question: does a 7-regular graph on 46 vertices with no 4-cycle exist?
# Labels (different from enc552.py): root r = 45; its neighbours 38..44; the e edges inside N(r)
# are (44,43), (42,41)[, (40,39)]; the private blocks B(u) of second neighbours are taken from
# the top down: B(44) first, ending at 0; far vertices (distance >= 3) are the lowest labels.
# C4-freeness: every two vertices have at most one common neighbour (clauses over pairs of
# common-neighbour candidates). Degrees: totalizer. Option TRI6: each vertex has at least 6
# incident edges lying in a triangle (z_vu <-> edge vu has a common neighbour).
import sys, itertools
import os
N, D, E = int(os.environ.get("NV", "46")), int(os.environ.get("DV", "7")), int(sys.argv[1]); TRI6 = int(sys.argv[2]); out = sys.argv[3]
TRIEDGES = int(os.environ.get('TRIEDGES', '6'))   # with TRI6: at least TRIEDGES incident edges lie in triangles
BLKC = os.environ.get('BLKC', '')                # per-block numbers of internal edges (order of nbr), e.g. 1212232
BLK = int(sys.argv[4]) if len(sys.argv) > 4 else 0      # every vertex in exactly 3 triangles: canonical blocks
CUBE = sys.argv[5] if len(sys.argv) > 5 else ''         # e.g. '0:emnemme' = (far0~far1?, types of B(44),B(43),...,B(38))
idx = {}
def X(a, b):
    if a > b: a, b = b, a
    return idx[(a, b)]
for a in range(N):
    for b in range(a+1, N):
        idx[(a, b)] = len(idx)+1
top = [len(idx)]
def fresh():
    top[0] += 1; return top[0]
F = {}  # forced values
r = N-1
nbr = list(range(N-2, N-2-D, -1))          # 44..38
match = {}
for t in range(E):
    a, b = nbr[2*t], nbr[2*t+1]
    match[a] = b; match[b] = a
for u in range(N-1):
    F[(min(u, r), max(u, r))] = u in nbr
for a, b in itertools.combinations(nbr, 2):
    F[(min(a, b), max(a, b))] = (match.get(a) == b)
cur = N-2-D                                # 37, going down
B = {}
for u in nbr:
    sz = D-1-(1 if u in match else 0)
    B[u] = list(range(cur, cur-sz, -1)); cur -= sz
farv = list(range(cur, -1, -1))
assert len(farv) == N-1-D-sum(len(v) for v in B.values())
for u in nbr:
    for w in range(0, N-1-D):
        F[(min(u, w), max(u, w))] = w in B[u]
if BLK:
    # B(u) listed top-down; for a matched u: first listed vertex = M-partner of u, then two edges
    # (2nd,3rd), (4th,5th); for the unmatched u: three edges (1st,2nd), (3rd,4th), (5th,6th).
    for u in nbr:
        bl = B[u]
        if u in match:
            want = {(bl[1], bl[2]), (bl[3], bl[4])}
        else:
            want = {(bl[0], bl[1]), (bl[2], bl[3]), (bl[4], bl[5])}
        want = {(min(a, b), max(a, b)) for a, b in want}
        for a, b in itertools.combinations(bl, 2):
            F[(min(a, b), max(a, b))] = (min(a, b), max(a, b)) in want
if BLKC:
    for u, cc in zip(nbr, BLKC):
        bl = B[u]; c = int(cc)
        if u in match:
            want = {(bl[1+2*i], bl[2+2*i]) for i in range(c)}
        else:
            want = {(bl[2*i], bl[2*i+1]) for i in range(c)}
        want = {(min(a, b), max(a, b)) for a, b in want}
        for a, b in itertools.combinations(bl, 2):
            F[(min(a, b), max(a, b))] = (min(a, b), max(a, b)) in want
units = []
if CUBE:
    adjf, types = CUBE.split(':')
    f0, f1 = farv[0], farv[1]        # farv = [1, 0] here: the cube is on vertex f1 = 0
    units.append(X(min(f0, f1), max(f0, f1)) * (1 if adjf == '1' else -1))
    for u, ty in zip(nbr, types):
        bl = B[u]
        if ty == 'n':
            units += [-X(min(f1, w), max(f1, w)) for w in bl]
        elif ty == 'e':
            units.append(X(min(f1, bl[1] if u in match else bl[0]), max(f1, bl[1] if u in match else bl[0])))
        elif ty == 'm':
            units.append(X(min(f1, bl[0]), max(f1, bl[0])))
C = []
def L(a, b, sign=1):
    p = (min(a, b), max(a, b))
    if p in F:
        return (F[p] if sign > 0 else (not F[p]))
    return X(a, b)*sign
def emit(lits):
    o = []
    for l in lits:
        if l is True: return
        if l is False: continue
        o.append(l)
    if not o: raise SystemExit('forced part is contradictory')
    C.append(o)
# at most one common neighbour for every pair {u, v}
for u, v in itertools.combinations(range(N), 2):
    others = [w for w in range(N) if w != u and w != v]
    for w, z in itertools.combinations(others, 2):
        emit([L(u, w, -1), L(v, w, -1), L(u, z, -1), L(v, z, -1)])
def totalizer(lits):
    # returns unary outputs o[0..n-1], o[i] <-> (at least i+1 of lits true)  (both directions)
    if len(lits) == 1: return [lits[0]]
    m = len(lits)//2
    A_, B_ = totalizer(lits[:m]), totalizer(lits[m:])
    o = [fresh() for _ in range(len(A_)+len(B_))]
    for i in range(len(A_)+1):
        for j in range(len(B_)+1):
            if i+j > 0:
                c = [o[i+j-1]]
                if i > 0: c.append(-A_[i-1])
                if j > 0: c.append(-B_[j-1])
                C.append(c)
            if i+j < len(o):
                c = [-o[i+j]]
                if i < len(A_): c.append(A_[i])
                if j < len(B_): c.append(B_[j])
                C.append(c)
    return o
for v in range(N):
    free = []; cnt = 0
    for u in range(N):
        if u == v: continue
        l = L(u, v)
        if l is True: cnt += 1
        elif l is not False: free.append(l)
    need = D-cnt
    if need < 0 or need > len(free): raise SystemExit('degree infeasible')
    if not free: continue
    o = totalizer(free)
    if need > 0: C.append([o[need-1]])
    if need < len(free): C.append([-o[need]])
if TRI6:
    for v in range(N):
        zs = []
        for u in range(N):
            if u == v: continue
            if L(u, v) is False: continue
            z = fresh(); zs.append(z)
            # z -> edge uv and some common neighbour w
            if L(u, v) is not True: C.append([-z, L(u, v)])
            ws = []
            for w in range(N):
                if w in (u, v): continue
                a1, a2 = L(v, w), L(u, w)
                if a1 is False or a2 is False: continue
                y = fresh(); ws.append(y)
                if a1 is not True: C.append([-y, a1])
                if a2 is not True: C.append([-y, a2])
            C.append([-z] + ws)
        if len(zs) < TRIEDGES: raise SystemExit('too few')
        o = totalizer(zs)
        C.append([o[TRIEDGES-1]])
for l in units: C.append([l])
with open(out, 'w') as f:
    f.write(f'p cnf {top[0]} {len(C)}\n')
    for c in C: f.write(' '.join(map(str, c)) + ' 0\n')
print('E', E, 'TRI6', TRI6, 'vars', top[0], 'clauses', len(C))
