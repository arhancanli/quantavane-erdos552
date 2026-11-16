#!/bin/sh
# Re-checks this repository.   sh checks/run_checks.sh [--quick | --full]
#   --quick (default): the witnesses (two 4-cycle tests, the non-neighbour bound, the Lean graph equals the edge list)
#                      and the red controls. Python 3 standard library only; a few seconds.
#   --full:            also the C checker, the Lean build (lake build) with a red Lean control, and the regeneration of
#                      every CNF formula with its SHA-256 compared to results/ (minutes; needs cc, elan and Python 3).
# The last line is "ALL PASS" only if every check passed.
cd "$(dirname "$0")/.." || exit 1
mode=${1:---quick}
fail=0
run() { echo "== $*"; "$@" || fail=1; }
run python3 -I checks/check_witness.py witness/w45_edges.txt --star 39 --lean lean/Erdos552/Lower39.lean
run python3 -I checks/check_witness.py witness/w58_edges.txt --star 51 --lean lean/Erdos552/Lower51.lean
run python3 -I checks/check_witness.py controls/w46_mindeg6_edges.txt --star 40
run python3 -I checks/check_witness.py controls/w48_afzaly_mckay_edges.txt --star 41
if [ "$mode" = --full ]; then
  tmp=$(mktemp -d)
  cc -O2 -o "$tmp/checkgraph" scripts/checkgraph.c || fail=1
  for w in witness/w45_edges.txt:6 witness/w58_edges.txt:7; do
    f=${w%:*}; d=${w#*:}; out=$("$tmp/checkgraph" "$f"); echo "== checkgraph $f: $out"
    echo "$out" | grep -q "mindeg=$d .*C4free=yes" || { echo "checkgraph: unexpected output"; fail=1; }
  done
  echo "== lake build (lean/)"
  out=$(cd lean && lake build 2>&1); echo "$out"
  n=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
  echo "$out" | grep -q "Build completed successfully" && [ "$n" = 2 ] || { echo "lean: build failed or unexpected axioms"; fail=1; }
  run python3 -I checks/red_controls.py --checkgraph "$tmp/checkgraph" --lean "lake env lean"
  run python3 -I tools/regen_cnfs.py all
  rm -rf "$tmp"
else
  run python3 -I checks/red_controls.py
fi
if [ $fail = 0 ]; then echo "ALL PASS"; else echo "SOME CHECK FAILED"; exit 1; fi
