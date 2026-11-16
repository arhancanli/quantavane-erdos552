/-
Erdős Problem #552: machine-checked lower bounds.

* `Erdos552.ramsey_C4_star39_gt_45`       : R(C₄, K_{1,39}) > 45 (a colouring of K₄₅ with no red C₄, no blue K_{1,39}).
* `Erdos552n51Lower.ramsey_C4_star51_gt_58` : R(C₄, K_{1,51}) > 58 (a colouring of K₅₈ with no red C₄, no blue K_{1,51}).

The upper bounds R(C₄, K_{1,39}) ≤ 46 and R(C₄, K_{1,51}) ≤ 59 are NOT proved in Lean; see README.md.
-/
import Erdos552.Lower39
import Erdos552.Lower51
