import ForestUnimodality.GaussianPade
import ForestUnimodality.RationalCompactification

/-! Real Gaussian directional envelopes. Rational-polynomial certificates
are connected to the actual exponential with its correct multiplier sign. -/
namespace ForestUnimodality.GaussianDirectionalEnvelope

open Real GaussianPade

noncomputable def kernel (y x theta : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (2 * y)) / Real.sqrt y * (1 - theta * x / y)

noncomputable def quadratic (H a B theta y x : ℝ) : ℝ :=
  H - (y - 1) / 2 - theta * x - a * x ^ 2 - B * (y - 1) ^ 2

def numerator3 (s x : ℝ) : ℝ := 960 * s ^ 6 - 240 * x ^ 2 * s ^ 4 + 24 * x ^ 4 * s ^ 2 - x ^ 6
def denominator3 (s x : ℝ) : ℝ := 960 * s ^ 6 + 240 * x ^ 2 * s ^ 4 + 24 * x ^ 4 * s ^ 2 + x ^ 6
def numerator2 (s x : ℝ) : ℝ := 48 * s ^ 4 - 12 * x ^ 2 * s ^ 2 + x ^ 4
def denominator2 (s x : ℝ) : ℝ := 48 * s ^ 4 + 12 * x ^ 2 * s ^ 2 + x ^ 4

noncomputable def cleared3 (H a B theta s x : ℝ) : ℝ :=
  (s ^ 2 - theta * x) * numerator3 s x -
    s ^ 3 * denominator3 s x * quadratic H a B theta (s ^ 2) x

noncomputable def cleared2 (H a B theta s x : ℝ) : ℝ :=
  (s ^ 2 - theta * x) * numerator2 s x -
    s ^ 3 * denominator2 s x * quadratic H a B theta (s ^ 2) x

theorem denominator3_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < denominator3 s x := by
  unfold denominator3
  positivity

theorem denominator2_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < denominator2 s x := by
  unfold denominator2
  positivity

theorem rational3_eq {s : ℝ} (hs : 0 < s) (x : ℝ) :
    numerator3 s x / denominator3 s x = P3 (x ^ 2 / (2 * s ^ 2)) / Q3 (x ^ 2 / (2 * s ^ 2)) := by
  have hp : numerator3 s x = (8 * s ^ 6) * P3 (x ^ 2 / (2 * s ^ 2)) := by
    unfold numerator3 P3
    field_simp
    ring
  have hq : denominator3 s x = (8 * s ^ 6) * Q3 (x ^ 2 / (2 * s ^ 2)) := by
    unfold denominator3 Q3
    field_simp
    ring
  rw [hp, hq, mul_div_mul_left _ _ (by positivity : 8 * s ^ 6 ≠ 0)]

theorem rational2_eq {s : ℝ} (hs : 0 < s) (x : ℝ) :
    numerator2 s x / denominator2 s x = P2 (x ^ 2 / (2 * s ^ 2)) / Q2 (x ^ 2 / (2 * s ^ 2)) := by
  have hp : numerator2 s x = (4 * s ^ 4) * P2 (x ^ 2 / (2 * s ^ 2)) := by
    unfold numerator2 P2
    field_simp
    ring
  have hq : denominator2 s x = (4 * s ^ 4) * Q2 (x ^ 2 / (2 * s ^ 2)) := by
    unfold denominator2 Q2
    field_simp
    ring
  rw [hp, hq, mul_div_mul_left _ _ (by positivity : 4 * s ^ 4 ≠ 0)]

theorem kernel_sq {s : ℝ} (hs : 0 < s) (x theta : ℝ) :
    kernel (s ^ 2) x theta = (s ^ 2 - theta * x) / s ^ 3 *
      Real.exp (-(x ^ 2 / (2 * s ^ 2))) := by
  unfold kernel
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hs]
  have hn : -x ^ 2 / (2 * s ^ 2) = -(x ^ 2 / (2 * s ^ 2)) := by ring
  rw [hn]
  field_simp

theorem lower_of_cleared3 {H a B theta s x : ℝ} (hs : 0 < s)
    (hsign : 0 ≤ s ^ 2 - theta * x) (hc : 0 ≤ cleared3 H a B theta s x) :
    quadratic H a B theta (s ^ 2) x ≤ kernel (s ^ 2) x theta := by
  have hd := denominator3_pos hs x
  have hpoly : quadratic H a B theta (s ^ 2) x ≤
      (s ^ 2 - theta * x) * numerator3 s x / (s ^ 3 * denominator3 s x) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hs _) hd)).mpr
    unfold cleared3 at hc
    nlinarith
  have hrat := P3_div_Q3_le_exp_neg (div_nonneg (sq_nonneg x) (by positivity : 0 ≤ 2 * s ^ 2))
  rw [← rational3_eq hs x] at hrat
  have hmul := mul_le_mul_of_nonneg_left hrat (div_nonneg hsign (pow_pos hs 3).le)
  rw [kernel_sq hs]
  apply hpoly.trans
  convert! hmul using 1
  ring

theorem lower_of_cleared2 {H a B theta s x : ℝ} (hs : 0 < s)
    (hsign : s ^ 2 - theta * x ≤ 0) (hc : 0 ≤ cleared2 H a B theta s x) :
    quadratic H a B theta (s ^ 2) x ≤ kernel (s ^ 2) x theta := by
  have hd := denominator2_pos hs x
  have hpoly : quadratic H a B theta (s ^ 2) x ≤
      (s ^ 2 - theta * x) * numerator2 s x / (s ^ 3 * denominator2 s x) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hs _) hd)).mpr
    unfold cleared2 at hc
    nlinarith
  have hrat := exp_neg_le_P2_div_Q2 (div_nonneg (sq_nonneg x) (by positivity : 0 ≤ 2 * s ^ 2))
  rw [← rational2_eq hs x] at hrat
  have hmul := mul_le_mul_of_nonpos_left hrat (div_nonpos_of_nonpos_of_nonneg hsign (pow_pos hs 3).le)
  rw [kernel_sq hs]
  apply hpoly.trans
  convert! hmul using 1
  ring

#print axioms lower_of_cleared3
#print axioms lower_of_cleared2
end ForestUnimodality.GaussianDirectionalEnvelope
