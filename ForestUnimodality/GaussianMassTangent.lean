import ForestUnimodality.AvailableEntropy
import ForestUnimodality.ExpEnclosure
import Mathlib.Analysis.Real.Sqrt

/-! A true Gaussian tangent retaining the random denominator, and its global
bad-event price. Zero available count is included by the real division convention. -/
namespace ForestUnimodality.GaussianMassTangent
open Real

theorem normalization {y : ℝ} (hy : 0 < y) :
    y * exp (-(3 / 2 : ℝ) * log y) = 1 / sqrt y := by
  have hs : exp (log y / 2) = sqrt y := by
    rw [← log_sqrt hy.le, exp_log (sqrt_pos.mpr hy)]
  calc
    y * exp (-(3 / 2 : ℝ) * log y) =
        exp (log y) * exp (-(3 / 2 : ℝ) * log y) := by rw [exp_log hy]
    _ = exp (-(log y / 2)) := by rw [← exp_add]; congr 1; ring
    _ = 1 / sqrt y := by rw [exp_neg, hs, one_div]

theorem lower {y x r : ℝ} (hy : 0 ≤ y) :
    exp (-r) * (y * (1 + r - (3 / 2) * log y) - x ^ 2 / 2) ≤
      exp (-x ^ 2 / (2 * y)) / sqrt y := by
  by_cases he : y = 0
  · subst y
    simp only [mul_zero, zero_mul, div_zero, exp_zero, sqrt_zero, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (neg_nonpos.mpr (by positivity))
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm he)
  let d := r - x ^ 2 / (2 * y) - (3 / 2) * log y
  have hh := mul_le_mul_of_nonneg_left (add_one_le_exp d)
    (mul_nonneg hy (exp_pos (-r)).le)
  have hleft : y * exp (-r) * (d + 1) =
      exp (-r) * (y * (1 + r - (3 / 2) * log y) - x ^ 2 / 2) := by
    dsimp [d]
    field_simp
    ring
  have hright : y * exp (-r) * exp d = exp (-x ^ 2 / (2 * y)) / sqrt y := by
    rw [mul_assoc, ← exp_add]
    have hd : -r + d = -(3 / 2 : ℝ) * log y + (-x ^ 2 / (2 * y)) := by dsimp [d]; ring
    rw [hd, exp_add, ← mul_assoc, normalization hyp]
    ring
  rwa [hleft, hright] at hh

theorem exp_neg_third_le : exp (-(1 / 3 : ℝ)) ≤ 43 / 60 := by
  have hc : ExpEnclosure.smallCheck (1 / 3) 12 (60 / 43) (7 / 5) = true := by decide +kernel
  have hh := (ExpEnclosure.smallCheck_sound hc).1
  norm_num at hh
  rw [exp_neg]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 60 / 43) hh
  norm_num at hi
  exact hi

theorem upper {y r : ℝ} (hy : 0 ≤ y) (hr : 0 ≤ r) :
    exp (-r) * y * (1 + r - (3 / 2) * log y) ≤ 43 / 40 := by
  by_cases he : y = 0
  · norm_num [he]
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm he)
  let b := exp ((2 * r - 1) / 3)
  have hb : 0 < b := exp_pos _
  have hl := one_sub_inv_le_log_of_pos (div_pos hyp hb)
  rw [log_div he hb.ne', log_exp] at hl
  have hmul := mul_le_mul_of_nonneg_left hl hy
  have hid : y * (1 - (y / b)⁻¹) = y - b := by field_simp
  rw [hid] at hmul
  have hscalar : y * (1 + r - (3 / 2) * log y) ≤ (3 / 2) * b := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hscalar (exp_pos (-r)).le
  have hid2 : exp (-r) * ((3 / 2) * b) = (3 / 2) * exp ((-r - 1) / 3) := by
    dsimp [b]
    rw [show exp (-r) * ((3 / 2) * exp ((2 * r - 1) / 3)) =
        (3 / 2) * (exp (-r) * exp ((2 * r - 1) / 3)) by ring, ← exp_add]
    congr 2
    ring
  rw [hid2] at hh
  have he' : exp ((-r - 1) / 3) ≤ exp (-(1 / 3 : ℝ)) := exp_le_exp.mpr (by linarith)
  nlinarith [exp_neg_third_le]

#print axioms lower
#print axioms upper
end ForestUnimodality.GaussianMassTangent
