import ForestUnimodality.GaussianDirectionalEnvelope
import ForestUnimodality.GaussianDirectionalDataHalfZero
import ForestUnimodality.GaussianDirectionalDataHalfNegative
import ForestUnimodality.GaussianDirectionalDataHalfMiddle
import ForestUnimodality.GaussianDirectionalDataHalfPositive

/-! The stage-350 theta=1/2 envelope on the full domain y>=4/9,
x real and |theta|<=1/2. Every one of its four unbounded regions is
connected to a complete kernel-checked rational certificate. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ForestUnimodality.GaussianDirectionalHalf

open GaussianDirectionalEnvelope RationalCompactification

theorem zero_identity (s x : ℝ) : evalSparse GaussianDirectionalDataHalfZero.terms s x =
    cleared3 (99 / 100) (3 / 5) 2 0 (s + 2 / 3) x := by
  norm_num [evalSparse, GaussianDirectionalDataHalfZero.terms, cleared3,
    quadratic, numerator3, denominator3]
  ring

theorem negative_identity (s x : ℝ) : evalSparse GaussianDirectionalDataHalfNegative.terms s x =
    cleared3 (99 / 100) (3 / 5) 2 (1 / 2) (s + 2 / 3) (-x) := by
  norm_num [evalSparse, GaussianDirectionalDataHalfNegative.terms, cleared3,
    quadratic, numerator3, denominator3]
  ring

theorem middle_identity (s x : ℝ) : evalSparse GaussianDirectionalDataHalfMiddle.terms s x =
    cleared3 (99 / 100) (3 / 5) 2 (1 / 2) (s + 2 / 3) (2 * (s + 2 / 3) ^ 2 * x) := by
  norm_num [evalSparse, GaussianDirectionalDataHalfMiddle.terms, cleared3,
    quadratic, numerator3, denominator3]
  ring

theorem positive_identity (s x : ℝ) : evalSparse GaussianDirectionalDataHalfPositive.terms s x =
    cleared2 (99 / 100) (3 / 5) 2 (1 / 2) (s + 2 / 3) (2 * (s + 2 / 3) ^ 2 + x) := by
  norm_num [evalSparse, GaussianDirectionalDataHalfPositive.terms, cleared2,
    quadratic, numerator2, denominator2]
  ring

theorem zero_envelope_sq {s : ℝ} (hs : 2 / 3 ≤ s) (x : ℝ) :
    quadratic (99 / 100) (3 / 5) 2 0 (s ^ 2) x ≤ kernel (s ^ 2) x 0 := by
  apply lower_of_cleared3 (by linarith : 0 < s) (by nlinarith [sq_nonneg s])
  by_cases hx : 0 ≤ x
  · have h := GaussianDirectionalDataHalfZero.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
      hx (by simp)
    simpa only [zero_identity, sub_add_cancel] using h
  · have h := GaussianDirectionalDataHalfZero.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
      (by linarith : 0 ≤ -x) (by simp)
    rw [zero_identity, sub_add_cancel] at h
    have he : cleared3 (99 / 100) (3 / 5) 2 0 s (-x) =
        cleared3 (99 / 100) (3 / 5) 2 0 s x := by
      unfold cleared3 quadratic numerator3 denominator3
      ring
    rwa [he] at h

theorem half_envelope_sq {s : ℝ} (hs : 2 / 3 ≤ s) (x : ℝ) :
    quadratic (99 / 100) (3 / 5) 2 (1 / 2) (s ^ 2) x ≤ kernel (s ^ 2) x (1 / 2) := by
  have hs0 : 0 < s := by linarith
  by_cases hx : x ≤ 0
  · apply lower_of_cleared3 hs0 (by nlinarith [sq_nonneg s])
    have h := GaussianDirectionalDataHalfNegative.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
      (by linarith : 0 ≤ -x) (by simp)
    simpa only [negative_identity, sub_add_cancel, neg_neg] using h
  · by_cases hupper : x ≤ 2 * s ^ 2
    · apply lower_of_cleared3 hs0 (by linarith)
      have hz : 0 ≤ x / (2 * s ^ 2) := div_nonneg (by linarith) (by positivity)
      have hz1 : x / (2 * s ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr hupper
      have h := GaussianDirectionalDataHalfMiddle.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
        hz (fun _ => hz1)
      rw [middle_identity, sub_add_cancel] at h
      have he : 2 * s ^ 2 * (x / (2 * s ^ 2)) = x := by field_simp
      rwa [he] at h
    · apply lower_of_cleared2 hs0 (by linarith)
      have h := GaussianDirectionalDataHalfPositive.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
        (by linarith : 0 ≤ x - 2 * s ^ 2) (by simp)
      rw [positive_identity, sub_add_cancel] at h
      have he : 2 * s ^ 2 + (x - 2 * s ^ 2) = x := by ring
      rwa [he] at h

theorem envelope_nonneg_theta {y theta : ℝ} (hy : 4 / 9 ≤ y)
    (ht : 0 ≤ theta) (ht1 : theta ≤ 1 / 2) (x : ℝ) :
    quadratic (99 / 100) (3 / 5) 2 theta y x ≤ kernel y x theta := by
  have hy0 : 0 ≤ y := by linarith
  have hs : 2 / 3 ≤ Real.sqrt y := by
    nlinarith [Real.sqrt_nonneg y, Real.sq_sqrt hy0]
  have h0 := zero_envelope_sq hs x
  have h1 := half_envelope_sq hs x
  rw [Real.sq_sqrt hy0] at h0 h1
  have h0' := mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ 1 - 2 * theta)
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * theta)
  have hq : quadratic (99 / 100) (3 / 5) 2 theta y x =
      (1 - 2 * theta) * quadratic (99 / 100) (3 / 5) 2 0 y x +
        2 * theta * quadratic (99 / 100) (3 / 5) 2 (1 / 2) y x := by unfold quadratic; ring
  have hk : kernel y x theta = (1 - 2 * theta) * kernel y x 0 +
      2 * theta * kernel y x (1 / 2) := by unfold kernel; ring
  rw [hq, hk]
  exact add_le_add h0' h1'

theorem envelope {y theta : ℝ} (hy : 4 / 9 ≤ y) (ht : |theta| ≤ 1 / 2) (x : ℝ) :
    quadratic (99 / 100) (3 / 5) 2 theta y x ≤ kernel y x theta := by
  by_cases ht0 : 0 ≤ theta
  · exact envelope_nonneg_theta hy ht0 (abs_le.mp ht).2 x
  · have hn := envelope_nonneg_theta hy (by linarith : 0 ≤ -theta)
      (by linarith [(abs_le.mp ht).1] : -theta ≤ 1 / 2) (-x)
    simpa [quadratic, kernel] using hn

#print axioms zero_identity
#print axioms negative_identity
#print axioms middle_identity
#print axioms positive_identity
#print axioms envelope
end ForestUnimodality.GaussianDirectionalHalf
