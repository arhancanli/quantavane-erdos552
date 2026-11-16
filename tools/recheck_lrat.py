#!/usr/bin/env python3
"""Re-solve formulas with CaDiCaL and check every LRAT certificate with an independent checker.

  CADICAL=/path/to/cadical LRATCHECK=/path/to/lrat-check python3 tools/recheck_lrat.py CNF_DIR NAME [NAME ...]
      [--work DIR]

CNF_DIR holds the formulas made by `python3 tools/regen_cnfs.py all --keep CNF_DIR`. For each NAME the formula
CNF_DIR/NAME.cnf is solved by CaDiCaL (--lrat=true --binary=false --vivifyinst=false; version 3.0.1 reproduces the
recorded certificates byte for byte), the certificate's SHA-256 is compared with the one recorded in results/ (when
there is one), the checker is run on (formula, certificate), and the certificate is deleted. LRATCHECK is drat-trim's
`lrat-check` (prints "c VERIFIED"); `cake_lpr` (prints "s VERIFIED UNSAT") also works.
One line per formula: NAME solver=... lrat_sha256=... recorded=match|DIFFERS|none checker=VERIFIED|FAILED secs=...
Exit status 0 only if every formula was UNSAT and every certificate was verified.
"""
import hashlib
import os
import re
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def recorded():
    rec = {}
    for sub in ("n39", "n51"):
        d = os.path.join(ROOT, "results", sub)
        for fn in os.listdir(d):
            for line in open(os.path.join(d, fn)):
                m = re.search(r"lrat_sha256=([0-9a-f]{64})", line)
                if m and not line.startswith("#"):
                    rec.setdefault(line.split()[0], m.group(1))
    return rec


def main():
    args = sys.argv[1:]
    work = None
    if "--work" in args:
        i = args.index("--work")
        work = args[i + 1]
        del args[i:i + 2]
    cnf_dir, names = args[0], args[1:]
    cadical = os.environ.get("CADICAL", "cadical")
    checker = os.environ.get("LRATCHECK", "lrat-check")
    rec = recorded()
    ok = True
    for name in names:
        cnf = os.path.join(cnf_dir, name + ".cnf")
        with tempfile.TemporaryDirectory(dir=work, prefix="lrat_") as tmp:
            proof = os.path.join(tmp, name + ".lrat")
            t0 = time.time()
            s = subprocess.run([cadical, "-q", "--lrat=true", "--binary=false", "--vivifyinst=false", cnf, proof],
                               capture_output=True, text=True)
            solver = next((ln[2:] for ln in s.stdout.splitlines() if ln.startswith("s ")), "NONE")
            h = hashlib.sha256()
            size = 0
            with open(proof, "rb") as f:
                for chunk in iter(lambda: f.read(1 << 22), b""):
                    h.update(chunk)
                    size += len(chunk)
            got = h.hexdigest()
            exp = rec.get(name)
            same = "none" if exp is None else ("match" if exp == got else "DIFFERS")
            c = subprocess.run([checker, cnf, proof], capture_output=True, text=True)
            out = c.stdout + c.stderr
            verified = c.returncode in (0, 20) and re.search(r"^(c|s) VERIFIED", out, re.M) is not None
            good = solver == "UNSATISFIABLE" and verified and same != "DIFFERS"
            ok &= good
            print(f"{name} solver={solver} lrat_bytes={size} lrat_sha256={got} recorded={same} "
                  f"checker={'VERIFIED' if verified else 'FAILED'} secs={time.time() - t0:.1f}", flush=True)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
