#!/usr/bin/env python3
"""Red controls: deliberately broken witnesses must be refused (Python 3 standard library only).

For each lower-bound witness this makes broken copies in a temporary folder and requires check_witness.py to refuse
every one of them:
  add_c4      one added edge x-y that closes a 4-cycle x-p-q-y (both 4-cycle tests are also run on it directly)
  drop_edge   one edge removed at a vertex of minimum degree (that vertex then has too many non-neighbours)
  dup_edge    one edge listed twice
  loop        one edge replaced by a loop
  header      the header announces one edge more than the file has
  lean_diff   the Lean file's `masks` changed by one added edge (the Lean graph no longer equals the edge list)
With --lean LEAN_CMD (for example "lake env lean", run from lean/) it also writes a copy of each Lean witness file with
the added edge of add_c4 and requires Lean to REJECT it (the kernel's `decide` must refute the broken colouring).
With --checkgraph BINARY it also requires the C checker scripts/checkgraph.c to report "C4free=NO" on add_c4.
Prints one line per control and "RED CONTROLS PASS" at the end only if every control was refused.
"""
import itertools
import os
import re
import shlex
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import check_witness as cw  # noqa: E402

WITNESSES = [  # (edge list, star n, Lean file)
    ("witness/w45_edges.txt", 39, "lean/Erdos552/Lower39.lean"),
    ("witness/w58_edges.txt", 51, "lean/Erdos552/Lower51.lean"),
]


def load(path):
    rows = [line.split() for line in open(path) if line.strip()]
    n_vert = int(rows[0][0])
    edges = [tuple(map(int, r)) for r in rows[1:]]
    return n_vert, edges


def write(path, n_vert, edges, m=None):
    with open(path, "w") as f:
        f.write(f"{n_vert} {len(edges) if m is None else m}\n")
        for a, b in edges:
            f.write(f"{a} {b}\n")


def c4_closing_pair(n_vert, edges):
    adj = [set() for _ in range(n_vert)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    for x in range(n_vert):
        for p in sorted(adj[x]):
            for q in sorted(adj[p] - {x}):
                for y in sorted(adj[q] - {x, p}):
                    if y not in adj[x] and x < y:
                        return x, y, adj
    raise SystemExit("no pair closes a 4-cycle (unexpected)")


def refused(edge_file, star, lean=None):
    cmd = [sys.executable, "-I", os.path.join(HERE, "check_witness.py"), edge_file, "--star", str(star)]
    if lean:
        cmd += ["--lean", lean]
    r = subprocess.run(cmd, capture_output=True, text=True)
    last = (r.stdout.strip().splitlines() or [""])[-1]
    return r.returncode != 0 and last.startswith("FAIL"), last


def lean_with_edge(src, dst, x, y):
    text = open(src, encoding="utf-8").read()
    m = re.search(r"(def masks : List Nat := \[)(.*?)(\])", text, re.S)
    vals = [int(v) for v in re.findall(r"\d+", m.group(2))]
    vals[x] |= 1 << y
    vals[y] |= 1 << x
    body = "\n  " + ",\n  ".join(str(v) for v in vals)
    open(dst, "w", encoding="utf-8").write(text[:m.start(2)] + body + text[m.end(2):])


def main():
    args = sys.argv[1:]
    lean_cmd = shlex.split(args[args.index("--lean") + 1]) if "--lean" in args else None
    cg = args[args.index("--checkgraph") + 1] if "--checkgraph" in args else None
    ok = True
    with tempfile.TemporaryDirectory(prefix="erdos552_red_") as tmp:
        for rel, star, lean_rel in WITNESSES:
            src = os.path.join(ROOT, rel)
            lean_src = os.path.join(ROOT, lean_rel)
            n_vert, edges = load(src)
            x, y, adj = c4_closing_pair(n_vert, edges)
            tag = os.path.basename(rel).split("_")[0]
            controls = {}
            # add_c4
            f = os.path.join(tmp, f"{tag}_add_c4.txt")
            write(f, n_vert, edges + [(x, y)])
            adj2 = [set(s) for s in adj]
            adj2[x].add(y)
            adj2[y].add(x)
            both = cw.c4_by_paths(adj2) is not None and cw.c4_by_brute_force(adj2) is not None
            controls[f"add_c4 (edge {x}-{y})"] = (f, both)
            # drop_edge at a vertex of minimum degree
            degs = [len(s) for s in adj]
            v = degs.index(min(degs))
            k = next(i for i, e in enumerate(edges) if v in e)
            f = os.path.join(tmp, f"{tag}_drop_edge.txt")
            write(f, n_vert, edges[:k] + edges[k + 1:])
            controls[f"drop_edge {edges[k][0]}-{edges[k][1]}"] = (f, True)
            # dup_edge, loop, header
            f = os.path.join(tmp, f"{tag}_dup_edge.txt")
            write(f, n_vert, edges + [edges[0]])
            controls["dup_edge"] = (f, True)
            f = os.path.join(tmp, f"{tag}_loop.txt")
            write(f, n_vert, [(edges[0][0], edges[0][0])] + edges[1:])
            controls["loop"] = (f, True)
            f = os.path.join(tmp, f"{tag}_header.txt")
            write(f, n_vert, edges, m=len(edges) + 1)
            controls["header"] = (f, True)
            for name, (f, extra) in controls.items():
                r, last = refused(f, star)
                good = r and extra
                ok &= good
                print(f"{rel} {name}: {'refused' if good else 'NOT REFUSED'} ({last})")
            # lean_diff: the original edge list against a Lean file with one added edge
            lf = os.path.join(tmp, os.path.basename(lean_src))
            lean_with_edge(lean_src, lf, x, y)
            r, last = refused(src, star, lean=lf)
            ok &= r
            print(f"{rel} lean_diff: {'refused' if r else 'NOT REFUSED'} ({last})")
            if cg:
                out = subprocess.run([cg, os.path.join(tmp, f"{tag}_add_c4.txt")], capture_output=True, text=True).stdout
                good = "C4free=NO" in out
                ok &= good
                print(f"{rel} add_c4 with checkgraph: {'refused' if good else 'NOT REFUSED'} ({out.strip()})")
            if lean_cmd:
                r = subprocess.run(lean_cmd + [lf], capture_output=True, text=True, cwd=os.path.join(ROOT, "lean"))
                msg = (r.stdout + r.stderr).strip().splitlines()
                err = next((m for m in msg if "error" in m), msg[0] if msg else "")
                good = r.returncode != 0 and "error" in (r.stdout + r.stderr)
                ok &= good
                print(f"{lean_rel} with edge {x}-{y} added: Lean {'REJECTS it' if good else 'ACCEPTS IT'} ({err[:150]})")
    print("RED CONTROLS PASS" if ok else "RED CONTROLS FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
