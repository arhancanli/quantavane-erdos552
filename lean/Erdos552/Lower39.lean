/-
Erdős Problem #552 (R(C₄, K_{1,n})), the case n = 39: the lower bound R(C₄, K_{1,39}) ≥ 46.

`red` below is a graph on the vertices 0, …, 44: the Erdős–Rényi polarity graph of PG(2,7) with 12
vertices deleted. It has no 4-cycle, and every vertex has at most 38 non-neighbours, so colouring
its edges red and the other pairs blue gives a colouring of K₄₅ with no red C₄ and no blue K_{1,39}.
Lean core only; every finite fact is checked by `decide` (kernel reduction); no `native_decide`.
-/

namespace Erdos552

/-- Bit `j` of `masks[i]` is set iff `i` and `j` are adjacent. -/
def masks : List Nat := [
  1108378452480,
  17661577660416,
  2340774494208,
  554189226240,
  4466800070688,
  2234456999952,
  17869213548672,
  8933600141376,
  17733649416,
  34084860461057,
  1117799858432,
  1237487747106,
  1374410514448,
  1134005719168,
  1172528170052,
  1651482560520,
  260046849,
  70875619584,
  9075274418208,
  17609374334996,
  2748787459202,
  4432955719744,
  138523185160,
  8323073,
  2474505212164,
  4537767232528,
  8865903116416,
  17630874378250,
  1090921693185,
  4406655322370,
  17600847283232,
  2207646908480,
  8804817453068,
  8321499137,
  8830721721600,
  2216607883296,
  335691794,
  306186372,
  18142227337280,
  4673193934856,
  65025,
  36525048356,
  9346421359120,
  4419588719232,
  276086391362]

/-- The red graph. -/
def red (u v : Nat) : Bool := (masks.getD u 0).testBit v

theorem red_symm : ∀ u < 45, ∀ v < 45, red u v = red v u := by decide

theorem red_irrefl : ∀ u < 45, red u u = false := by decide

/-- Two distinct vertices have at most one common neighbour. -/
theorem common_le_one : ∀ a < 45, ∀ c < 45, a ≠ c →
    ((List.range 45).filter (fun w => red a w && red c w)).length ≤ 1 := by decide

/-- Every vertex has at most 38 non-neighbours (other than itself). -/
theorem nonnbrs_le : ∀ v < 45,
    ((List.range 45).filter (fun w => w != v && !red v w)).length ≤ 38 := by decide

theorem two_le_length {l : List Nat} {b d : Nat} (hb : b ∈ l) (hd : d ∈ l) (h : b ≠ d) :
    2 ≤ l.length := by
  have h1 := List.length_erase_of_mem hb
  have hd' : d ∈ l.erase b := (List.mem_erase_of_ne (Ne.symm h)).2 hd
  have h2 := List.length_pos_of_mem hd'
  have h3 := List.length_pos_of_mem hb
  omega

/-- No red 4-cycle: there are no vertices a, b, c, d < 45 with a ≠ c, b ≠ d and red edges ab, bc, cd, da. -/
theorem no_red_C4 : ∀ a b c d : Nat, a < 45 → b < 45 → c < 45 → d < 45 → a ≠ c → b ≠ d →
    red a b = true → red b c = true → red c d = true → red d a = true → False := by
  intro a b c d ha hb hc hd hac hbd h1 h2 h3 h4
  have h2' : red c b = true := by rw [red_symm c hc b hb]; exact h2
  have h4' : red a d = true := by rw [red_symm a ha d hd]; exact h4
  have mb : b ∈ (List.range 45).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hb, h1, h2']
  have md : d ∈ (List.range 45).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hd, h4', h3]
  have := two_le_length mb md hbd
  have := common_le_one a ha c hc hac
  omega

/-- R(C₄, K_{1,39}) > 45: a 2-colouring of the pairs of {0, …, 44} with no red 4-cycle and no
blue star with 39 leaves (blue = not red). -/
theorem ramsey_C4_star39_gt_45 : ∃ col : Nat → Nat → Bool,
    (∀ u < 45, ∀ v < 45, col u v = col v u) ∧
    (∀ a b c d : Nat, a < 45 → b < 45 → c < 45 → d < 45 → a ≠ c → b ≠ d →
      col a b = true → col b c = true → col c d = true → col d a = true → False) ∧
    (∀ v < 45, ((List.range 45).filter (fun w => w != v && !col v w)).length ≤ 38) :=
  ⟨red, red_symm, no_red_C4, nonnbrs_le⟩

end Erdos552

#print axioms Erdos552.ramsey_C4_star39_gt_45

