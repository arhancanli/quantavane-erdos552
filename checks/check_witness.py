#!/usr/bin/env python3
"""Check a lower-bound witness for R(C4, K_{1,n}) > N (Python 3 standard library only).

A graph G on N vertices gives a red/blue colouring of K_N (edges of G red, the other pairs blue). That colouring
has no red C4 and no blue K_{1,n} exactly when
  (1) G has no 4-cycle, and
  (2) every vertex has at most n - 1 non-neighbours, i.e. minimum degree >= N - n.

This program was written separately from scripts/checkgraph.c (the C checker used when the witnesses were found).
It tests (1) twice, by two different methods:
  (a) every path a - b - c (a < c) is recorded under the pair {a, c}; a second middle vertex for the same pair
      closes a 4-cycle;
  (b) brute force: for every 4-set {a, b, c, d} the three possible 4-cycles a-b-c-d, a-b-d-c, a-c-b-d are tested.
With --lean FILE it also reads the list `masks` from a Lean witness file and checks that the graph in the Lean file
is exactly the graph in the edge list.

Usage: check_witness.py EDGES --star n [--lean FILE.lean]
EDGES: first line "N m", then m lines "a b" with 0 <= a, b < N.
Exit status 0 and a last line "PASS" only if every test holds; otherwise "FAIL: reason" and exit status 1.
"""
import itertools
import re
import sys


def fail(msg):
    print("FAIL: " + msg)
    sys.exit(1)


def read_edges(path):
    with open(path, encoding="ascii") as f:
        rows = [line.split() for line in f if line.strip()]
    if not rows or len(rows[0]) != 2:
        fail("first line must be 'N m'")
    n_vert, m = int(rows[0][0]), int(rows[0][1])
    edges = rows[1:]
    if len(edges) != m:
        fail(f"header says {m} edges, file has {len(edges)}")
    adj = [set() for _ in range(n_vert)]
    for k, row in enumerate(edges):
        if len(row) != 2:
            fail(f"edge line {k + 2} is not 'a b'")
        a, b = int(row[0]), int(row[1])
        if not (0 <= a < n_vert and 0 <= b < n_vert):
            fail(f"edge {a} {b} has a vertex outside 0..{n_vert - 1}")
        if a == b:
            fail(f"loop at vertex {a}")
        if b in adj[a]:
            fail(f"edge {a} {b} is listed twice")
        adj[a].add(b)
        adj[b].add(a)
    return n_vert, m, adj


def c4_by_paths(adj):
    middle = {}
    for b, nb in enumerate(adj):
        for a, c in itertools.combinations(sorted(nb), 2):
            if (a, c) in middle:
                return (a, middle[(a, c)], c, b)
            middle[(a, c)] = b
    return None


def c4_by_brute_force(adj):
    n_vert = len(adj)
    for a, b, c, d in itertools.combinations(range(n_vert), 4):
        for p, q, r, s in ((a, b, c, d), (a, b, d, c), (a, c, b, d)):
            if q in adj[p] and r in adj[q] and s in adj[r] and p in adj[s]:
                return (p, q, r, s)
    return None


def lean_masks(path):
    text = open(path, encoding="utf-8").read()
    m = re.search(r"def masks : List Nat := \[(.*?)\]", text, re.S)
    if not m:
        fail(f"no 'def masks : List Nat := [...]' in {path}")
    return [int(x) for x in re.findall(r"\d+", m.group(1))]


def main():
    args = sys.argv[1:]
    if not args or "--star" not in args:
        print(__doc__)
        sys.exit(2)
    path = args[0]
    star = int(args[args.index("--star") + 1])
    lean = args[args.index("--lean") + 1] if "--lean" in args else None

    n_vert, m, adj = read_edges(path)
    degs = [len(nb) for nb in adj]
    print(f"{path}: N = {n_vert}, edges = {m}, degrees {min(degs)}..{max(degs)}")

    cyc = c4_by_paths(adj)
    if cyc:
        fail(f"4-cycle {cyc} (path method)")
    print("no 4-cycle (path method): ok")
    cyc = c4_by_brute_force(adj)
    if cyc:
        fail(f"4-cycle {cyc} (brute force over all 4-sets)")
    print("no 4-cycle (brute force over all 4-sets): ok")

    worst = max(n_vert - 1 - d for d in degs)
    if worst > star - 1:
        v = degs.index(min(degs))
        fail(f"vertex {v} has {n_vert - 1 - degs[v]} non-neighbours: a blue K_(1,{star}) exists")
    print(f"most non-neighbours of any vertex = {worst} <= {star - 1}: no blue K_(1,{star}): ok")

    if lean:
        masks = lean_masks(lean)
        if len(masks) != n_vert:
            fail(f"Lean masks has {len(masks)} entries, the edge list has {n_vert} vertices")
        for v in range(n_vert):
            from_lean = {j for j in range(n_vert) if (masks[v] >> j) & 1}
            if masks[v] >> n_vert:
                fail(f"Lean mask of vertex {v} has a bit at or above {n_vert}")
            if from_lean != adj[v]:
                fail(f"Lean mask of vertex {v} differs from the edge list")
        print(f"{lean}: the graph in `masks` equals the edge list: ok")

    print(f"R(C4, K_(1,{star})) > {n_vert} certified by this graph")
    print("PASS")


if __name__ == "__main__":
    main()
