/-
Erdős Problem #552 (R(C₄, K_{1,n})), the case n = 51: the lower bound R(C₄, K_{1,51}) > 58.
With the SAT/LRAT upper bound described in README.md this gives R(C₄, K_{1,51}) = 59.

`red` is a graph on the vertices 0, …, 57 (the Erdős–Rényi polarity graph of PG(2,8) minus its 9 absolute points, the pole of their line, and 5 points
of a line through that pole; `scripts/er8_58.py`). It has no 4-cycle and every vertex has at most 50 non-neighbours, so colouring its edges red and the
other pairs blue gives a colouring of K_58 with no red C₄ and no blue K_{1,51}.
Lean core only; every finite fact is checked by `decide` (kernel reduction); no `native_decide`.
-/

namespace Erdos552n51Lower

/-- Bit `j` of `masks[i]` is set iff `i` and `j` are adjacent. -/
def masks : List Nat := [
  16256,
  149537943584912,
  36100265295757472,
  18300273681268928,
  72057877774729346,
  9042452482621572,
  5067134233215112,
  127,
  72622743149873153,
  1130332583645185,
  144124053429460993,
  9078122049962241,
  18156244132954625,
  36310289243177985,
  4582781913924100,
  72097180789244936,
  17454747090944,
  37154839197646850,
  9148076602165248,
  4785212078694416,
  18014553262670088,
  144150544247161376,
  563095999382532,
  2234207627640832,
  18034224149823492,
  4522295754788864,
  9029206683951106,
  17935818031392,
  72075188908605968,
  144133330286281792,
  285978576338026496,
  2534443290198024,
  2322202951321602,
  2815041829081104,
  2287542599704576,
  2254003150783040,
  3386498095252512,
  8323072,
  144189963590762512,
  36301600524352,
  36029348955885572,
  72347899484242176,
  10133374106698248,
  4646604858541058,
  1065353216,
  72198898472484896,
  144396942233847812,
  18058378983247874,
  72569923837960,
  5629508136730944,
  36596213746893312,
  136365211648,
  9578946409021504,
  4507998814996512,
  144255926655782920,
  73184594530279428,
  36066181756518672,
  18085043744277504]

/-- The red graph. -/
def red (u v : Nat) : Bool := (masks.getD u 0).testBit v

theorem red_symm : ∀ u < 58, ∀ v < 58, red u v = red v u := by decide

theorem red_irrefl : ∀ u < 58, red u u = false := by decide

/-- Two distinct vertices have at most one common neighbour. -/
theorem common_le_one : ∀ a < 58, ∀ c < 58, a ≠ c →
    ((List.range 58).filter (fun w => red a w && red c w)).length ≤ 1 := by decide

/-- Every vertex has at most 50 non-neighbours (other than itself). -/
theorem nonnbrs_le : ∀ v < 58,
    ((List.range 58).filter (fun w => w != v && !red v w)).length ≤ 50 := by decide

theorem two_le_length {l : List Nat} {b d : Nat} (hb : b ∈ l) (hd : d ∈ l) (h : b ≠ d) :
    2 ≤ l.length := by
  have h1 := List.length_erase_of_mem hb
  have hd' : d ∈ l.erase b := (List.mem_erase_of_ne (Ne.symm h)).2 hd
  have h2 := List.length_pos_of_mem hd'
  have h3 := List.length_pos_of_mem hb
  omega

/-- No red 4-cycle. -/
theorem no_red_C4 : ∀ a b c d : Nat, a < 58 → b < 58 → c < 58 → d < 58 → a ≠ c → b ≠ d →
    red a b = true → red b c = true → red c d = true → red d a = true → False := by
  intro a b c d ha hb hc hd hac hbd h1 h2 h3 h4
  have h2' : red c b = true := by rw [red_symm c hc b hb]; exact h2
  have h4' : red a d = true := by rw [red_symm a ha d hd]; exact h4
  have mb : b ∈ (List.range 58).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hb, h1, h2']
  have md : d ∈ (List.range 58).filter (fun w => red a w && red c w) := by
    simp [List.mem_filter, List.mem_range, hd, h4', h3]
  have := two_le_length mb md hbd
  have := common_le_one a ha c hc hac
  omega

/-- R(C₄, K_{1,51}) > 58: a 2-colouring of the pairs of {0, …, 57} with no red 4-cycle and no blue star
with 51 leaves (blue = not red). -/
theorem ramsey_C4_star51_gt_58 : ∃ col : Nat → Nat → Bool,
    (∀ u < 58, ∀ v < 58, col u v = col v u) ∧
    (∀ a b c d : Nat, a < 58 → b < 58 → c < 58 → d < 58 → a ≠ c → b ≠ d →
      col a b = true → col b c = true → col c d = true → col d a = true → False) ∧
    (∀ v < 58, ((List.range 58).filter (fun w => w != v && !col v w)).length ≤ 50) :=
  ⟨red, red_symm, no_red_C4, nonnbrs_le⟩

end Erdos552n51Lower

#print axioms Erdos552n51Lower.ramsey_C4_star51_gt_58

