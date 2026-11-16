# Erdős Problem #552: R(C₄, K₁,₃₉) = 46 and R(C₄, K₁,₅₁) = 59

This repository gives proofs of two values of the Ramsey numbers f(n) = R(C₄, K₁,ₙ):

* **f(39) = 46** (the published bounds were 46 ≤ f(39) ≤ 47);
* **f(51) = 59** (the published bounds were 59 ≤ f(51) ≤ 60).

**These values are not first claimed here.** Both were posted before us, in public repositories that describe
themselves as not yet reviewed: f(39) = 46 by
[suitedaces/ramsey-c4-star39](https://github.com/suitedaces/ramsey-c4-star39) (July 2026), and f(39) = 46 and
f(51) = 59 by [zach7036/c4-star-ramsey](https://github.com/zach7036/c4-star-ramsey) (August 2026). See
[History and credits](#history-and-credits). Our proofs were found independently, on 12 November 2026, before we
knew of those repositories, and we offer them as an independent confirmation. For n = 39 our proof is, like
suitedaces's, a counting reduction followed by a SAT case analysis, with its own case split, encodings and
certificates. For n = 51 it is a SAT case analysis, a different kind of proof from zach7036's eigenvalue argument.

What is here: the two lower-bound graphs, with Lean 4 proofs; the upper-bound arguments written out in full; the
programs that build every SAT formula of the case analysis, with two separately written encodings; the SHA-256 of
every formula and every LRAT certificate; and scripts that re-check the parts that fit on a laptop.

Author: Arhan Canli (Quantavane, arhan@quantavane.com). On the use of AI, see [AI use](#ai-use).

## The problem

Erdős Problem #552 ([erdosproblems.com/552](https://www.erdosproblems.com/552)) asks for the Ramsey number
R(C₄, Sₙ), where Sₙ = K₁,ₙ is the star with n leaves. It also asks whether, for every c > 0, infinitely many n
satisfy R(C₄, Sₙ) ≤ n + √n − c. This repository says nothing about the second question.

R(C₄, K₁,ₙ) is the least N such that every red/blue colouring of the edges of the complete graph K_N contains a red 4-cycle or a blue
star K₁,ₙ. Take the red edges as a graph G on N vertices. A blue K₁,ₙ is a vertex with n non-neighbours in G. So:

> f(n) > N if and only if some graph on N vertices has no 4-cycle and minimum degree at least N − n.

So f(39) = 46 means: (a) some C₄-free graph on 45 vertices has minimum degree 6, and (b) no C₄-free graph on 46
vertices has minimum degree 7. Likewise f(51) = 59 means: (a) some C₄-free graph on 58 vertices has minimum degree
7, and (b) no C₄-free graph on 59 vertices has minimum degree 8.

## History and credits

* T. D. Parsons (Trans. Amer. Math. Soc. 209, 1975) proved the general upper bound f(n) ≤ n + ⌈√n⌉ + 1. Exact
  values for families of n near q² come from the polarity graphs of projective planes (Parsons, and later papers).
* Further exact values and families: Wu, Sun, Zhang and Radziszowski (Graphs Combin. 31, 2015); Zhang, Chen and
  Cheng (Discrete Math. 340, 2017; Finite Fields Appl. 45, 2017).
* L. Boza, *Exact values and bounds for Ramsey numbers of C₄ versus a star graph*,
  [arXiv:2409.12770](https://arxiv.org/abs/2409.12770) (v2, 12 June 2026), settled the eight values with n ≤ 38
  that were still unknown, and proved general inequalities. Its table gives 59/60 for n = 51; its Proposition 11
  gives the lower bound f(51) ≥ 59.
* S. Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1, revision 18 (24 April 2026),
  Table IVa lists f(39) as 46–47. Every other value with n ≤ 41 is listed as known there.
* **Earlier public claims of the same two values** (not peer-reviewed, as their authors say):
  * [suitedaces/ramsey-c4-star39](https://github.com/suitedaces/ramsey-c4-star39), created 24 July 2026: f(39) = 46.
    A 45-vertex lower-bound graph; for the upper bound, a counting reduction, symmetry and 12 CNF instances, each with
    an LRAT certificate checked by drat-trim's `lrat-check` and by the verified checker `cake_lpr`.
  * [zach7036/c4-star-ramsey](https://github.com/zach7036/c4-star-ramsey), created 1 August 2026: f(39) = 46 and
    f(51) = 59, and also f(83) ≤ 93. For n = 39 it gives the same regularity count (with a parity lemma that rules out
    our case A by hand) and then an exact spectral argument, plus a separate SAT analysis. For n = 51 it gives an
    algebraic eigenvalue argument with no SAT at all.
  * An independent audit of zach7036's f(39) proof, dated 11 August 2026, in
    [pw/erdosproblemaday-verification](https://github.com/pw/erdosproblemaday-verification) (folder `552/`), reports
    PASS for the finite theorem.

  We found these repositories by a search made after our computation, on 12 November 2026. Our work did not use
  them. Our counting lemma for n = 39 agrees with theirs, as it must. The rest of our case analysis, the encodings,
  the witnesses and the Lean files were made separately.
* Status when this repository was made (16 November 2026): the teorth/erdosproblems database (`problems.yaml`) lists
  #552 as open, last updated 2025-08-31. OEIS [A006672](https://oeis.org/A006672) gives terms up to n = 38. arXiv
  has no version of Boza's paper after v2, and an arXiv search found no newer paper on these values.

## Lower bounds: the two graphs

| value | file | vertices, edges | degrees | construction |
| --- | --- | --- | --- | --- |
| f(39) ≥ 46 | `witness/w45_edges.txt` | 45, 148 | 6 to 8 | polarity graph ER₇ of PG(2,7) (57 vertices) minus 12 vertices |
| f(51) ≥ 59 | `witness/w58_edges.txt` | 58, 212 | 7 to 8 | polarity graph ER₈ of PG(2,8) (73 vertices) minus 15 vertices |

Both bounds were already known (see above). The files are edge lists: a first line `N m`, then one edge `a b` per
line, vertices numbered from 0.

* `w45_edges.txt` comes from `scripts/witness45.py 1`, a random local search for 12 vertices of ER₇ whose deletion
  leaves minimum degree 6 (seed 1 reproduces the file byte for byte).
* `w58_edges.txt` comes from `scripts/er8_58.py`, a fixed construction. In ER₈ (x ~ y when x·y = 0 and x ≠ y, over
  GF(8) = GF(2)[t]/(t³+t+1)) the absolute points form the line ℓ: x₁+x₂+x₃ = 0, with pole p = (1,1,1). Delete ℓ and
  p. The remaining 63 vertices all have degree 8, since each has exactly one neighbour on ℓ. Then delete 5 of the 7
  points of a line L through p that lie neither at p nor on ℓ. Two of these points span L, whose pole lies on ℓ, so they
  have no common neighbour left; every remaining vertex loses at most one neighbour, and the minimum degree is 7.

Each graph has no 4-cycle, and each vertex has at most 38 (resp. 50) non-neighbours. Colour its edges red and the
other pairs blue: there is no red C₄ and no blue K₁,₃₉ (resp. K₁,₅₁).

**Machine checks.**
* Lean 4 (v4.35.0, core library only, no Mathlib): `lean/Erdos552/Lower39.lean` proves
  `Erdos552.ramsey_C4_star39_gt_45` and `lean/Erdos552/Lower51.lean` proves
  `Erdos552n51Lower.ramsey_C4_star51_gt_58`. Each states that some 2-colouring of the pairs of {0, …, N−1} is
  symmetric, has no red 4-cycle and has no vertex with n blue neighbours. Every finite fact is checked by `decide`
  (kernel reduction; no `native_decide`). Both theorems depend only on the axioms `propext`, `Classical.choice` and
  `Quot.sound`. The build output is in `results/lean_build.txt`.
* `checks/check_witness.py` (Python, standard library) tests each edge list for 4-cycles twice, by two different
  methods, checks the non-neighbour bound, and checks that the graph in the Lean file is exactly the edge list.
* `scripts/checkgraph.c` is the C checker used when the graphs were found. It prints the minimum degree and the
  largest number of common neighbours of two vertices.
* Red controls (`checks/red_controls.py`): broken copies of each witness must be refused. These include one added
  edge that closes a 4-cycle, one edge removed at a vertex of minimum degree, a duplicate edge, a loop, a wrong edge
  count, and a Lean file whose graph differs from the edge list by one edge. With `--lean`, Lean must also reject the
  colouring with the added edge.

## Upper bound for n = 39: no C₄-free graph on 46 vertices has minimum degree 7

Let G be a C₄-free graph on 46 vertices with minimum degree at least 7. We derive a contradiction.

**Lemma 1 (counting).** Let v be a vertex of degree d, let N(v) be its neighbourhood, and let e be the number of edges
inside N(v), which is the number of triangles through v.

1. N(v) spans a matching. If u ∈ N(v) had two neighbours w, w′ in N(v), then v w u w′ would be a 4-cycle.
2. For u ∈ N(v) put A(u) = N(u) ∖ ({v} ∪ N(v)). These sets are pairwise disjoint: a vertex x in A(u) ∩ A(u′) would
   give the 4-cycle v u x u′.
3. |A(u)| = d(u) − 1 − m(u), where m(u) ∈ {0, 1} is the number of neighbours of u inside N(v). Summing over N(v):
   Σ|A(u)| ≥ 7d − d − 2e = 6d − 2e ≥ 5d, since e ≤ ⌊d/2⌋. The sets A(u) lie in V ∖ ({v} ∪ N(v)), which has
   45 − d vertices. So 5d ≤ 45 − d, and d ≤ 7.

So **G is 7-regular**. Then Σ|A(u)| = 42 − 2e ≤ 38 gives **e ∈ {2, 3}**: every vertex lies in 2 or 3 triangles.
A vertex outside {v} ∪ N(v) and outside every A(u) is at distance at least 3 from v; call it *far*. There are
38 − (42 − 2e) = 2e − 4 far vertices: none when e = 2, two when e = 3.

**Labelling.** Given a vertex with e triangles we may call it 0, its neighbours 1, …, 7 with the edges 1–2, 3–4 (and
5–6 when e = 3) inside N(0), and the sets A(1), …, A(7) consecutive intervals of 8, 9, … in this order (5 vertices
for a matched u, 6 for an unmatched one), with the far vertices last. This fixes every adjacency of the vertices
0, …, 7.

**Case A: some vertex lies in exactly 2 triangles.** Call it 0. The formula says: the adjacencies of 0, …, 7 are as
above, there is no 4-cycle, and every vertex has degree exactly 7. *Unsatisfiable.*

**Case B: every vertex lies in exactly 3 triangles.** Take any vertex as 0. Then A(1), …, A(6) have 5 vertices,
A(7) has 6, and 44 and 45 are far.

*Lemma 2.* For u ∈ N(0), the edges inside N(u) are 0–p(u), where p(u) is the partner of a matched u, and the edges
inside A(u). No vertex x of A(u) is adjacent to 0, by definition, or to p(u), because 0 u x p(u) would be a
4-cycle. Since u lies in exactly 3 triangles, A(u) spans exactly 2 edges for u = 1, …, 6 and exactly 3 for u = 7,
and these edges form a matching (part 1 of Lemma 1, applied at u). Relabelling inside each block, they are
(s, s+1), (s+2, s+3), and (s+4, s+5) for A(7), where s is the first vertex of the block. The formula also says that
every vertex lies in at least 3 triangles.

*Lemma 3.* The far vertex 44 is at distance at least 3 from 0, so it is adjacent to none of 0, …, 7. It has at most one neighbour in each block, since two
neighbours x, y in A(u) would give the 4-cycle u x 44 y. Its 7 neighbours are therefore either 45 and one vertex in
each of 6 blocks, or one vertex in each of the 7 blocks. The relabellings of a block that keep its matching are
transitive on the block's matched vertices. So 44's neighbour in A(u) may be taken to be the first vertex of the
block (type `e`) or its unmatched last vertex (type `m`, blocks 1 to 6 only). This gives 320 patterns: 2⁶ = 64 with
44 ~ 45 and no neighbour in A(7), 6 · 2⁵ = 192 with 44 ~ 45 and no neighbour in one of A(1), …, A(6), and 2⁶ = 64
with 44 ≁ 45. The 48 symmetries of vertex 0 permute the pairs {1,2}, {3,4}, {5,6} together with their blocks, and swap
the two vertices of a pair together with their blocks. They reduce the 320 patterns to **32 orbits**. Each orbit
gives one formula: the base formula plus unit clauses for 44's neighbourhood. *All 32 are unsatisfiable.*

Hence no such G exists, so f(39) ≤ 46. With the lower bound, **f(39) = 46**. A by-product: no 7-regular graph on 46
vertices is C₄-free.

## Upper bound for n = 51: no C₄-free graph on 59 vertices has minimum degree 8

Let G be a C₄-free graph on 59 vertices with minimum degree at least 8.

**Step 1 (counting).** Lemma 1, with 59 vertices and degrees at least 8, gives Σ|A(u)| ≥ 7d − 2e ≥ 6d and
Σ|A(u)| ≤ 58 − d. So 7d ≤ 58, d ≤ 8, and **G is 8-regular**. Then 56 − 2e ≤ 50 gives **e ∈ {3, 4}**: every vertex
lies in 3 or 4 triangles, with 2e − 6 far vertices (none if e = 3).

**Step 2 (divisibility).** Not every vertex lies in 4 triangles. If they all did, counting (vertex, triangle)
incidences would give 3T = 59 · 4 = 236, which is not a multiple of 3. So some vertex lies in exactly 3 triangles.

**Step 3 (ten patterns).** Call that vertex the root. Its neighbourhood has 3 matched pairs and 2 unmatched vertices.
There are no far vertices, and the blocks A(u), with 6 vertices for a matched u and 7 for an unmatched u, partition
the other 50 vertices. As in Lemma 2, the number of triangles at u ∈ N(root) is [u matched] + c_u, where c_u is the
number of edges inside A(u), which form a matching. That number is 3 or 4, so c_u ∈ {2, 3} for a matched u. For an
unmatched u, c_u = 3, because 7 vertices hold at most 3 disjoint edges. We relabel each block so that its edges are
consecutive pairs. Up to the 48 symmetries of the root, the values (c_u) for the six matched u form **10 patterns**:
A00, …, A09. *Patterns A00–A08, in which some matched c_u = 2, are unsatisfiable.*

**Step 4 (a constraint derived from A00–A08).** Any vertex in exactly 3 triangles can serve as the root. So once
A00–A08 are refuted, G has no vertex w in exactly 3 triangles with a triangle-neighbour x (a matched vertex of N(w))
that also lies in exactly 3 triangles: with w as the root, x would have c_x = 2. In the last pattern A09 (all
c_u = 3), each of the two unmatched neighbours of the root lies in exactly 3 triangles. So each of the 6 + 6 matched
vertices of their two blocks lies in 4 triangles, which means every edge at such a vertex lies in a triangle. We add
this to A09.

**Step 5 (split of A09).** Let z₁ and z₂ be the unmatched vertices of the two 7-vertex blocks. Take z₁. Its
neighbour in N(root) is its own unmatched root-neighbour, and only that one: a second would be a second common
neighbour of z₁ and the root. It has no neighbour in its own block (the edges
inside a block are exactly its three matching edges, which miss z₁), there are no far vertices, and it has at most one
neighbour in any other block. So z₁ has exactly one neighbour in each of the other 7 blocks, and the same holds for
z₂. Up to relabelling inside blocks:

* z₁'s neighbour in each 6-vertex block (a perfect matching) is the block's first vertex b₀. In the other 7-vertex
  block it is a matched vertex (we take the first) or z₂.
* z₂'s neighbour in a 6-vertex block is b₀ (type 0), b₀'s partner b₁ (type 1) or one of the other four (type 2; the
  relabellings that fix b₀ are transitive on them). At most one block has type 0, since z₁ and z₂ have at most one
  common neighbour. In z₁'s block, z₂'s neighbour is z₁ when z₁ ~ z₂, and otherwise we take it to be the block's
  first vertex.

Up to the 48 root symmetries this leaves 22 type words with z₁ ~ z₂ and 22 without: **44 sub-cases**. *All 44 are
unsatisfiable.*

Hence f(51) ≤ 59, and with the lower bound **f(51) = 59**. In particular, no 8-regular graph on 59 vertices is
C₄-free.

## The SAT pieces

There are 33 formulas for n = 39 (case A, then the 32 orbits of case B). There are 53 formulas for n = 51 (A00–A08,
then the 44 sub-cases of A09). Every formula was built twice, by two encoders written separately:

| | encoding 1 | encoding 2 |
| --- | --- | --- |
| programs | `enc552.py`, `cubes552.py` (n = 39); `cubesA51a.py`, `refineA51a.py`, `splitA09a.py` (n = 51) | `enc552b.py`, `cubes552b.py` (n = 39); `cubesA51.py`, `refineA51.py`, `splitA09.py` (n = 51) |
| labels | root 0, blocks numbered upward | root N−1, blocks numbered downward, far vertices lowest |
| no 4-cycle | one clause per 4-cycle (three per 4-set) | "at most one common neighbour" clauses |
| degrees | sequential counters | totalizers |
| at least 3 triangles at each vertex (case B; n = 51) | a variable per (vertex, pair) and a counter | "at least 6 incident edges lie in a triangle" |

For each case split, the orbit representatives were computed by the two programs separately: one by a canonical
form (the multiset of pairs), the other by the lexicographic minimum over the 48 listed symmetries. For every split the
two programs give the same orbits (checked).

**Results** (all tables in `results/`, one line per formula with its CNF SHA-256 and, where a certificate was
checked, the LRAT SHA-256 and the number of checked steps):

| | encoding 1 | encoding 2 |
| --- | --- | --- |
| n = 39, case A | UNSAT, LRAT checked (15,279 steps) | UNSAT, LRAT checked (12,874 steps) |
| n = 39, 32 orbits | all UNSAT with CaDiCaL 3.0.1 (1,882 s in all); **no certificate kept** | all UNSAT with CaDiCaL 2.1.2 (203 s); all 32 LRAT certificates from CaDiCaL 3.0.1 checked (4,963,149 steps, largest 377,753) |
| n = 51, 53 pieces | all UNSAT, all 53 LRAT checked (15,586,175 steps) | all UNSAT, all 53 LRAT checked (8,059,440 steps) |

So every piece of both proofs has a checked LRAT certificate in encoding 2, and n = 51 has one in encoding 1 as well.
The certificates were produced by CaDiCaL 3.0.1 (`--lrat=true --binary=false --vivifyinst=false`) and checked by our
own LRAT checker `tools/lratcheck.c` (strict: every hint must be a unit or falsifying clause; run with
`--skip-satisfied-hints`). The proof was streamed from the solver into the checker and into SHA-256, so no file had
to be stored; the n = 39 certificates of encoding 2 were also kept, gzip-compressed (233 MB, hashes in
`results/n39/proof_files.txt`).

**Second checker.** On 16 November 2026 every recorded certificate (142 in all, with the two 44-vertex controls) was
made again from the regenerated formulas with CaDiCaL 3.0.1. Each came out byte for byte the recorded one (same SHA-256),
and drat-trim's `lrat-check` (M. Heule), a checker we did not write, verified every one
(`results/lrat_recheck_drattrim.txt`). Red controls were refused by both checkers: a certificate without its
empty-clause step, a certificate whose last step cites a non-unit clause, and a formula with one clause removed.
`cake_lpr` has not been run.

**Controls of the encoders.**
* Known-negative control near full size: the same encoders at 44 vertices (both encodings UNSAT, LRAT checked;
  `results/n39/lrat_small.txt`, `lrat_red_control_enc2_44.txt`). Counting forces case e = 3 there, so this
  re-derives the published f(37) ≤ 44.
* Green controls: small regular C₄-free graphs are found (the Petersen graph at (10, 3), and (15, 4), (26, 5)).
  On the small instances of `results/n39/green_controls.txt`, wherever both runs finished, the symmetry-broken cases
  are satisfiable exactly when the unrestricted formula is.
* Full-size green control: a 7-regular C₄-free graph on 48 vertices in which every vertex lies in 3 triangles,
  from the public data of Afzaly and McKay (users.cecs.anu.edu.au/~bdm/data/extremal.html, file
  `extremal/c4_n48e168.maybe.s6`, 10th graph; `controls/w48_afzaly_mckay_edges.txt`). `scripts/canon48.py` relabels
  it into each encoder's fixed layout and fixes every edge variable. In our runs (CaDiCaL 3.0.1) both case-e = 3
  formulas at 48 vertices were then satisfiable: both encoders accept a real graph of this shape two vertices above
  the n = 39 size. To repeat it for encoding 2: `NV=48 python3 scripts/enc552b.py 3 1 b48.cnf 1`, then
  `python3 scripts/canon48.py controls/w48_afzaly_mckay_edges.txt b 0 units.txt`, and append the unit clauses.
* A C₄-free graph on 46 vertices with minimum degree 6 exists (`controls/w46_mindeg6_edges.txt`, from
  `scripts/witness46_d6.py 2`; consistent with the published f(40) = 47). So the n = 39 impossibility is specific to
  minimum degree 7.

## Re-checking

Quick checks (seconds; Python 3 only): witnesses, red controls.

```sh
sh checks/run_checks.sh --quick      # last line: ALL PASS
```

Full checks: also the Lean build with a red Lean control (needs [elan](https://github.com/leanprover/elan), which reads
`lean/lean-toolchain` and installs Lean v4.35.0), the C checker, and the regeneration of every CNF formula with its
SHA-256 compared to the tables (a few minutes, about 1 GB of temporary disk):

```sh
sh checks/run_checks.sh --full       # last line: ALL PASS
```

**Re-checking the SAT pieces.** The LRAT files are large (from a few MB to a few hundred MB each, several GB in all),
so they are not stored here. To regenerate and re-check one:

```sh
python3 tools/regen_cnfs.py all --keep cnf      # every formula into cnf/n39, cnf/n51_enc2, cnf/n51_enc1
F=cnf/n39/bcube004_0_eeemmme.cnf
cadical --lrat=true --binary=false --vivifyinst=false $F p.lrat   # CaDiCaL 3.0.1
shasum -a 256 p.lrat                            # equals lrat_sha256 in results/n39/lrat_cubes_enc2.txt
lrat-check $F p.lrat                            # drat-trim's LRAT checker
cake_lpr $F p.lrat                              # the verified CakeML checker
cc -O2 -o lratcheck tools/lratcheck.c && ./lratcheck --skip-satisfied-hints $F p.lrat
```

`tools/recheck_lrat.py` does the solve, hash comparison and check for a list of formulas (set `CADICAL` and
`LRATCHECK`), deleting each certificate after it is checked.

CaDiCaL is deterministic for a fixed version and options. In our tests on pieces of the neighbouring cases n = 41 and
n = 42, runs on Linux with a separately built CaDiCaL 3.0.1 reproduced the macOS LRAT bytes exactly. The n = 51 sub-case formulas are the refined A09
formula plus one unit clause per literal printed by `splitA09.py` (resp. `splitA09a.py`); `tools/regen_cnfs.py` builds
them in exactly that format.

## What is machine-checked, and what is a written argument

* **Machine-checked:** the two lower-bound graphs (Lean kernel; also two programs and the red controls), and the
  unsatisfiability of every SAT piece (LRAT certificates checked by two checkers, ours and drat-trim's
  `lrat-check`, for every piece in at least one encoding; the second encoding and a second solver version give the
  same answers).
* **Written arguments, not formalised:** Lemma 1 and Steps 1–2 (counting and divisibility); Lemmas 2–3 and
  Steps 3–5 (the structure of the blocks, the far vertex, the derived constraint and the split); the claim that each
  "we may take" is a genuine symmetry. The orbit lists themselves are computed, by two separate programs for each
  split. These arguments are elementary and short, and are written out above to be read line by line.
* **Trusted, not proved:** that each CNF formula says what the text says (the encoders). This is tested by the
  controls above but not proved. Also trusted: the LRAT checkers (two independent ones agree).
* **Not in Lean:** the upper bounds. A Lean proof would need the LRAT certificates checked in the kernel; at these
  sizes that is beyond `decide`.

## Repository layout

```text
witness/     the two lower-bound graphs (edge lists)
lean/        Lean 4 proofs of the two lower bounds (core only; lake build)
scripts/     encoders, case splits, witness constructions, the C graph checker, the 48-vertex relabeller
tools/       regen_cnfs.py (rebuild and hash every formula), recheck_lrat.py (re-solve, hash and check certificates),
             lratcheck.c (our LRAT checker)
results/     per-formula results: CNF and LRAT SHA-256, checked steps, solver times; the drat-trim re-check;
             the Lean build output
controls/    control graphs (46 vertices with minimum degree 6; the 48-vertex Afzaly–McKay graph)
checks/      check_witness.py, red_controls.py, run_checks.sh
SHA256SUMS   SHA-256 of every file above
```

## AI use

The searches, the SAT encodings, the case splits, all programs and scripts, the Lean files and this text were
produced with Claude (Anthropic), an AI system, working under the direction of Arhan Canli. No step should be taken
on trust from that. The claims rest on the machine checks described above (the Lean kernel for the lower bounds,
checked LRAT certificates for every SAT piece, two separately written encodings, red and green controls) and on the
short written arguments in this file, which can be checked by hand.

## Licence and citation

Text, graphs and tables: CC BY 4.0 (`LICENSE`). Programs: MIT (`LICENSE-CODE`). Please cite as: Arhan Canli,
*Erdős Problem #552: R(C₄, K₁,₃₉) = 46 and R(C₄, K₁,₅₁) = 59*, https://github.com/arhancanli/quantavane-erdos552
(2026), and cite the earlier claims and the literature above.
