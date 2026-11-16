#!/usr/bin/env python3
"""Regenerate every CNF formula of the two upper-bound proofs and compare its SHA-256 with the results tables.

  python3 tools/regen_cnfs.py [n39|n51|all] [--keep DIR]

Without --keep each formula is written to a temporary folder, hashed and deleted (peak disk use about 1 GB).
With --keep DIR the formulas are kept in DIR/n39, DIR/n51_enc2 and DIR/n51_enc1 (about 6 GB in all), ready for a SAT
solver. (Separate folders: the two n = 51 encodings use names that differ only in case, A00_... and a00_..., which
would overwrite each other on a case-insensitive disk such as the macOS default.)
The generators are deterministic, so every hash must equal the one recorded when the proofs were made.
Prints one line per formula and "CNF HASHES: k of k match" at the end; exit status 0 only if all match.
"""
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = os.path.join(ROOT, "scripts")
RES = os.path.join(ROOT, "results")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def table_hashes():
    want = {}
    for sub in ("n39", "n51"):
        for fn in sorted(os.listdir(os.path.join(RES, sub))):
            for line in open(os.path.join(RES, sub, fn)):
                if line.startswith("#") or not line.strip():
                    continue
                m = re.search(r"cnf_sha256=([0-9a-f]{64})", line)
                if m:
                    want.setdefault(line.split()[0], m.group(1))
                    continue
                m = re.match(r"([0-9a-f]{64})\s+(\S+)\.cnf$", line.strip())
                if m and fn.startswith("cnf_sha256"):
                    want.setdefault(m.group(2), m.group(1))
    return want


def run(args, env=None, out=None):
    e = dict(os.environ)
    for k in ("NV", "DV", "TRIEDGES", "BLKC"):
        e.pop(k, None)
    e.update(env or {})
    r = subprocess.run([sys.executable, "-I"] + args, env=e, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"generator failed: {' '.join(args)}\n{r.stdout}{r.stderr}")
    return r.stdout


def append_units(base, units, dst):
    # the sub-cube format used for the n = 51 runs: header updated, body of the base, one unit clause per line
    with open(base) as f:
        head, body = f.read().split("\n", 1)
    nv, nc = map(int, head.split()[2:4])
    with open(dst, "w") as f:
        f.write(f"p cnf {nv} {nc + len(units)}\n")
        f.write(body)
        for lit in units:
            f.write(f"{lit} 0\n")


class Checker:
    def __init__(self, keep):
        self.want = table_hashes()
        self.keep = keep
        self.n = self.ok = 0

    def check(self, path, name=None, delete=True, group="n39"):
        name = name or os.path.basename(path)[:-4]
        got = sha(path)
        exp = self.want.get(name)
        self.n += 1
        good = exp == got
        self.ok += good
        print(f"{name:24s} {got[:16]}  {'match' if good else ('NO RECORD' if exp is None else 'MISMATCH')}")
        if self.keep:
            os.makedirs(os.path.join(self.keep, group), exist_ok=True)
            shutil.copy(path, os.path.join(self.keep, group, os.path.basename(path)))
        if delete:
            os.remove(path)


def n39(c, tmp):
    p = lambda *a: os.path.join(tmp, *a)  # noqa: E731
    # encoding 1 (enc552.py; root 0, blocks upward)
    run([f"{S}/enc552.py", "46", "7", "2", p("c46_e2.cnf")]); c.check(p("c46_e2.cnf"))
    run([f"{S}/enc552.py", "44", "7", "3", p("c44_e3.cnf")]); c.check(p("c44_e3.cnf"))
    run([f"{S}/enc552.py", "46", "7", "3", p("c46_e3b.cnf"), "3", "1"])
    run([f"{S}/cubes552.py", p("c46_e3b.cnf"), p("cubes1")])
    c.check(p("c46_e3b.cnf"))
    for f in sorted(os.listdir(p("cubes1"))):
        c.check(p("cubes1", f))
    # encoding 2 (enc552b.py; root 45, blocks downward)
    run([f"{S}/enc552b.py", "2", "0", p("b46_e2.cnf")]); c.check(p("b46_e2.cnf"))
    run([f"{S}/enc552b.py", "3", "0", p("b44_e3.cnf")], env={"NV": "44"}); c.check(p("b44_e3.cnf"))
    run([f"{S}/enc552b.py", "3", "1", p("b46_e3b.cnf"), "1"])
    run([f"{S}/cubes552b.py", p("b46_e3b.cnf"), p("cubes2")])
    c.check(p("b46_e3b.cnf"))
    for f in sorted(os.listdir(p("cubes2"))):
        c.check(p("cubes2", f))


def n51(c, tmp):
    p = lambda *a: os.path.join(tmp, *a)  # noqa: E731
    env2 = {"NV": "59", "DV": "8", "TRIEDGES": "6"}
    # encoding 2: base, ten patterns, refined last pattern, 44 sub-cubes
    run([f"{S}/enc552b.py", "3", "1", p("b59_e3.cnf")], env=env2)
    run([f"{S}/cubesA51.py", p("b59_e3.cnf"), p("cA51")])
    c.check(p("b59_e3.cnf"), name="n51_enc2_base", group="n51_enc2")
    run([f"{S}/refineA51.py", p("cA51", "A09_33333333.cnf"), p("A09r.cnf")], env=env2)
    for f in sorted(os.listdir(p("cA51"))):
        if not f.startswith("A09"):
            c.check(p("cA51", f), group="n51_enc2")
    os.remove(p("cA51", "A09_33333333.cnf"))  # only its refinement A09r is used (and hashed below)
    for line in run([f"{S}/splitA09.py"]).splitlines():
        name, *units = line.split()
        append_units(p("A09r.cnf"), units, p(name + ".cnf"))
        c.check(p(name + ".cnf"), group="n51_enc2")
    c.check(p("A09r.cnf"), name="n51_enc2_A09_refined", group="n51_enc2")
    # encoding 1: the same steps with the separately written programs
    run([f"{S}/enc552.py", "59", "8", "3", p("c59_e3.cnf"), "3"])
    run([f"{S}/cubesA51a.py", p("c59_e3.cnf"), p("ca")])
    os.remove(p("c59_e3.cnf"))
    run([f"{S}/refineA51a.py", p("ca", "a09_33333333.cnf"), p("a09r.cnf")])
    for f in sorted(os.listdir(p("ca"))):
        if not f.startswith("a09"):
            c.check(p("ca", f), group="n51_enc1")
    for line in run([f"{S}/splitA09a.py"]).splitlines():
        name, *units = line.split()
        append_units(p("a09r.cnf"), units, p(name + ".cnf"))
        c.check(p(name + ".cnf"), group="n51_enc1")


def main():
    args = sys.argv[1:]
    which = next((a for a in args if a in ("n39", "n51", "all")), "all")
    keep = args[args.index("--keep") + 1] if "--keep" in args else None
    if keep:
        os.makedirs(keep, exist_ok=True)
    c = Checker(keep)
    # three extra hashes recorded in the n = 51 notes (base, unrefined and refined last pattern of encoding 2)
    c.want.update({
        "n51_enc2_base": "18988c5987bb3907e04221e69bbe72d7dfc5cba65839f0e763fa05a61eb78d20",
        "n51_enc2_A09_refined": "7492d299926242e307fa38f3cebbc55c1e6ac1e8c9671c8ada33feaf33253c53",
    })
    with tempfile.TemporaryDirectory(prefix="erdos552_cnf_") as tmp:
        if which in ("n39", "all"):
            n39(c, tmp)
        if which in ("n51", "all"):
            n51(c, tmp)
    print(f"CNF HASHES: {c.ok} of {c.n} match")
    sys.exit(0 if c.ok == c.n else 1)


if __name__ == "__main__":
    main()
