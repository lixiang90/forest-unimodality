import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Scalar induction step for normalized ranks of a hereditary family in a
product of rank-one factors. This does not assume or prove that a graph has
already been encoded as such a family. -/

namespace ForestUnimodality

/-- Combining the absent section and all present sections preserves the
normalized adjacent-rank inequality. q0,q1,q2 are three consecutive ranks of
the smaller reference product and d is the number of colors in the new factor.
The inclusion of every present section in the absent section supplies hsubset.
-/
theorem normalized_rank_extension_step
    {q0 q1 q2 a0 a1 b0 b1 d : ℝ}
    (hq0 : 0 ≤ q0) (hq1 : 0 < q1) (hq2 : 0 ≤ q2) (hd : 0 ≤ d)
    (hlog : q0 * q2 ≤ q1 ^ 2)
    (ha : a1 * q1 ≤ a0 * q2)
    (hb : b1 * q0 ≤ b0 * q1)
    (hsubset : b1 ≤ d * a0) :
    (a1 + b1) * (q1 + d * q0) ≤ (a0 + b0) * (q2 + d * q1) := by
  have hA := mul_le_mul_of_nonneg_right ha
    (add_nonneg hq1.le (mul_nonneg hd hq0))
  have hB := mul_le_mul_of_nonneg_right hb
    (add_nonneg hq2 (mul_nonneg hd hq1.le))
  have hC := mul_le_mul_of_nonneg_right hsubset (sub_nonneg.mpr hlog)
  have hp : ((a1 + b1) * (q1 + d * q0)) * q1 ≤
      ((a0 + b0) * (q2 + d * q1)) * q1 := by nlinarith
  exact le_of_mul_le_mul_right hp hq1

#print axioms normalized_rank_extension_step
end ForestUnimodality
