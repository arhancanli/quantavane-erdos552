#!/usr/bin/env python3
# Second, independent case split for case e=3 (layout of enc552b.py: root 45, N(root) = 44..38,
# pairs (44,43),(42,41),(40,39), unmatched 38; blocks B(44)=37..33, B(43)=32..28, B(42)=27..23,
# B(41)=22..18, B(40)=17..13, B(39)=12..8, B(38)=7..2; far vertices 1 and 0; the split is on vertex 0).
# Orbits: the 48 symmetries of the root (permute the 3 pairs, swap inside pairs) act on the 6 types.
import sys, itertools, os
base, outdir = sys.argv[1], sys.argv[2]
N = 46
idx = {}
for a in range(N):
    for b in range(a+1, N):
        idx[(a, b)] = len(idx)+1
def X(a, b): return idx[(min(a, b), max(a, b))]
nbr = [44, 43, 42, 41, 40, 39, 38]
B = {44: [37,36,35,34,33], 43: [32,31,30,29,28], 42: [27,26,25,24,23], 41: [22,21,20,19,18],
     40: [17,16,15,14,13], 39: [12,11,10,9,8], 38: [7,6,5,4,3,2]}
group = []
for perm in itertools.permutations(range(3)):
    for sw in itertools.product((0, 1), repeat=3):
        def g(t, perm=perm, sw=sw):
            prs = [(t[0], t[1]), (t[2], t[3]), (t[4], t[5])]
            out = []
            for k in range(3):
                p = prs[perm[k]]
                out += [p[1], p[0]] if sw[k] else [p[0], p[1]]
            return tuple(out)
        group.append(g)
assert len(group) == 48
reps = []
for adj in (0, 1):
    for t in itertools.product('nem', repeat=6):
        for t7 in 'ne':
            nn = list(t).count('n') + (t7 == 'n')
            if nn != adj: continue
            if min(g(t) for g in group) != t: continue
            reps.append((adj, ''.join(t) + t7))
os.makedirs(outdir, exist_ok=True)
lines = open(base).read().split('\n', 1)
nv, nc = map(int, lines[0].split()[2:4])
for k, (adj, ty) in enumerate(reps):
    units = [X(0, 1) if adj else -X(0, 1)]
    for u, c in zip(nbr, ty):
        bl = B[u]; matched = (u != 38)
        if c == 'n': units += [-X(0, w) for w in bl]
        elif c == 'e': units.append(X(0, bl[1] if matched else bl[0]))
        else: units.append(X(0, bl[0]))
    with open(os.path.join(outdir, f'bcube{k:03d}_{adj}_{ty}.cnf'), 'w') as f:
        f.write(f'p cnf {nv} {nc+len(units)}\n'); f.write(lines[1])
        if not lines[1].endswith('\n'): f.write('\n')
        for l in units: f.write(f'{l} 0\n')
print(len(reps), 'cubes:', ' '.join(f'{a}:{t}' for a, t in reps))
