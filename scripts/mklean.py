#!/usr/bin/env python3
# Write a core-Lean file proving R(C4, K_{1,n}) > N from a witness edge list (first line "N m").
# Usage: mklean.py WITNESS n NAMESPACE > File.lean
import sys
w, n, ns = sys.argv[1], int(sys.argv[2]), sys.argv[3]
lines = open(w).read().split('\n')
N, m = map(int, lines[0].split())
adj = [0]*N
for l in lines[1:]:
    if not l.strip(): continue
    a, b = map(int, l.split()); adj[a] |= 1 << b; adj[b] |= 1 << a
masks = ',\n  '.join(str(x) for x in adj)
print(f'''/-
Erdős Problem #552 (R(C₄, K_{{1,n}})), the case n = {n}: the lower bound R(C₄, K_{{1,{n}}}) > {N}.

`red` is a graph on the vertices 0, …, {N-1} (the Erdős–Rényi polarity graph of PG(2,7) with {57-N} vertices
deleted). It has no 4-cycle and every vertex has at most {n-1} non-neighbours, so colouring its edges red and the
other pairs blue gives a colouring of K_{N} with no red C₄ and no blue K_{{1,{n}}}.
Lean core only; every finite fact is checked by `decide` (kernel reduction); no `native_decide`.
-/

namespace {ns}

/-- Bit `j` of `masks[i]` is set iff `i` and `j` are adjacent. -/
def masks : List Nat := [
  {masks}]

/-- The red graph. -/
def red (u v : Nat) : Bool := (masks.getD u 0).testBit v

theorem red_symm : ∀ u < {N}, ∀ v < {N}, red u v = red v u := by decide

theorem red_irrefl : ∀ u < {N}, red u u = false := by decide

/-- Two distinct vertices have at most one common neighbour. -/
theorem common_le_one : ∀ a < {N}, ∀ c < {N}, a ≠ c →
    ((List.range {N}).filter (fun w => red a w && red c w)).length ≤ 1 := by decide

/-- Every vertex has at most {n-1} non-neighbours (other than itself). -/
theorem nonnbrs_le : ∀ v < {N},
    ((List.range {N}).filter (fun w => w != v && !red v w)).length ≤ {n-1} := by decide

theorem two_le_length {{l : List Nat}} {{b d : Nat}} (hb : b ∈ l) (hd : d ∈ l) (h : b ≠ d) :
    2 ≤ l.length := by
  have h1 := List.length_erase_of_mem hb
  have hd' : d ∈ l.erase b := (List.mem_erase_of_ne (Ne.symm h)).2 hd
  have h2 := List.length_pos_of_mem hd'
  have h3 := List.length_pos_of_mem hb
  omega

/-- No red 4-cycle. -/
theorem no_red_C4 : ∀ a b c d : Nat, a < {N} → b < {N} → c < {N} → d < {N} → a ≠ c → b ≠ d →
    red a b = true → red b c = true → red c d = true → red d a = true → False := by
  intro a b c d ha hb hc hd hac hbd h1 h2 h3 h4
  have h2' : red c b = true := by rw [red_symm c hc b hb]; exact h2
  have h4' : red a d = true := by rw [red_symm a ha d hd]; exact h4
  have mb : b ∈ (List.range {N}).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hb, h1, h2']
  have md : d ∈ (List.range {N}).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hd, h4', h3]
  have := two_le_length mb md hbd
  have := common_le_one a ha c hc hac
  omega

/-- R(C₄, K_{{1,{n}}}) > {N}: a 2-colouring of the pairs of {{0, …, {N-1}}} with no red 4-cycle and no blue star
with {n} leaves (blue = not red). -/
theorem ramsey_C4_star{n}_gt_{N} : ∃ col : Nat → Nat → Bool,
    (∀ u < {N}, ∀ v < {N}, col u v = col v u) ∧
    (∀ a b c d : Nat, a < {N} → b < {N} → c < {N} → d < {N} → a ≠ c → b ≠ d →
      col a b = true → col b c = true → col c d = true → col d a = true → False) ∧
    (∀ v < {N}, ((List.range {N}).filter (fun w => w != v && !col v w)).length ≤ {n-1}) :=
  ⟨red, red_symm, no_red_C4, nonnbrs_le⟩

end {ns}

#print axioms {ns}.ramsey_C4_star{n}_gt_{N}
''')
