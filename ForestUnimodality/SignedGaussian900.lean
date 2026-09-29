import ForestUnimodality.SignedGaussianContact
import ForestUnimodality.SignedGaussianNumeric900

/-! The fixed full-domain stage-900 signed Gaussian lower envelope, with
all optimizer bracketing and transcendental constants proved in Lean. -/
namespace ForestUnimodality.SignedGaussian900
open Set Real SignedGaussianMinimum SignedGaussianProfile SignedGaussianHermite SignedGaussianContact

noncomputable def parameter : ℝ := (11 / 5) * exp (-(2 / 5 : ℝ))

theorem parameter_bounds : 0 < parameter ∧ parameter < 3 := by
  have h := contact_parameter (x₀ := 2 / 5) (by norm_num)
  norm_num [SignedGaussianMinimum.slope, parameter] at h ⊢
  exact h

theorem third_negative_power : (1 / 3 : ℝ) ^ (-(3 / 2 : ℝ)) = 3 * sqrt 3 := by
  rw [rpow_neg_eq_inv_rpow]
  norm_num only [one_div, inv_inv]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (by norm_num), rpow_one,
    ← sqrt_eq_rpow]

theorem third_five_halves : (1 / 3 : ℝ) ^ (5 / 2 : ℝ) = 1 / (9 * sqrt 3) := by
  have hs : 0 < sqrt (3 : ℝ) := sqrt_pos.2 (by norm_num)
  have he : (1 / 3 : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / 3 : ℝ) ^ (5 / 2 : ℝ) = 1 / 3 := by
    rw [← rpow_add (by norm_num)]
    norm_num
  rw [third_negative_power] at he
  apply (eq_div_iff (mul_pos (by norm_num : (0 : ℝ) < 9) hs).ne').mpr
  nlinarith

theorem cutoff_slope : SignedGaussianMinimum.slope (4 / 3) ≤
    parameter * (1 / 3 : ℝ) ^ (5 / 2 : ℝ) := by
  have hs : 0 < sqrt (3 : ℝ) := sqrt_pos.2 (by norm_num)
  have hmargin := SignedGaussianNumeric900.slope_margin
  have hm : ((15 / 11 : ℝ) * sqrt 3) * exp (-(4 / 3 : ℝ)) <
      exp (14 / 15) * exp (-(4 / 3 : ℝ)) := by
    apply mul_lt_mul_of_pos_right (by linarith) (exp_pos _)
  have he : exp (14 / 15 : ℝ) * exp (-(4 / 3 : ℝ)) = exp (-(2 / 5 : ℝ)) := by
    rw [← exp_add]
    norm_num
  rw [he] at hm
  rw [third_five_halves]
  unfold SignedGaussianMinimum.slope parameter
  norm_num
  have hbound : (1 / 3 : ℝ) * exp (-(4 / 3 : ℝ)) ≤
      ((11 / 5 : ℝ) * exp (-(2 / 5 : ℝ))) / (9 * sqrt 3) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 9) hs)).mpr
    nlinarith
  convert! hbound using 1
  ring

theorem cutoff_profile_lower : -(11 / 3 : ℝ) * sqrt 3 * exp (-(4 / 3 : ℝ)) ≤ profile parameter (1 / 3) := by
  have hc := parameter_bounds
  have hbranch : parameter * (1 / 3 : ℝ) ^ (5 / 2 : ℝ) < 3 := by
    have hp : (1 / 3 : ℝ) ^ (5 / 2 : ℝ) ≤ 1 := rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    exact (mul_le_of_le_one_right hc.1.le hp).trans_lt hc.2
  have h := profile_lower_of_slope_bound hc.1 (by norm_num : (0 : ℝ) < 1 / 3)
    hbranch (u := 4 / 3) (by norm_num) cutoff_slope
  rw [third_negative_power] at h
  norm_num [contactValue] at h
  nlinarith

theorem coefficient_lower : (-5 : ℝ) ≤ coefficient parameter (1 / 3) := by
  have hc := parameter_bounds
  rw [coefficient_eq_quotient hc.1 hc.2 (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)]
  have hp := source_900_contact.2.1
  have hf := source_900_contact.2.2
  change profile parameter 1 = _ at hp
  change first parameter 1 = _ at hf
  rw [hp, hf]
  have hm := SignedGaussianNumeric900.curvature_margin
  have hl := cutoff_profile_lower
  norm_num
  nlinarith

theorem tight_coefficient_lower : (-(4813 / 1000) : ℝ) ≤ coefficient parameter (1 / 3) := by
  have hc := parameter_bounds
  rw [coefficient_eq_quotient hc.1 hc.2 (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)]
  have hp := source_900_contact.2.1
  have hf := source_900_contact.2.2
  change profile parameter 1 = _ at hp
  change first parameter 1 = _ at hf
  rw [hp, hf]
  have hm := SignedGaussianNumeric900.tight_curvature_margin
  have hl := cutoff_profile_lower
  norm_num
  nlinarith

theorem envelope {y x : ℝ} (hy : 1 / 3 ≤ y) (hx : 0 ≤ x) :
    exp (-(2 / 5 : ℝ)) * ((27 / 25 : ℝ) + (29 / 50) * (y - 1) - (11 / 5) * y * x) -
      5 * (y - 1) ^ 2 ≤ y ^ (-(3 / 2 : ℝ)) * (1 - 2 * x) * exp (-x) := by
  have hK : (-5 : ℝ) ≤ coefficient (SignedGaussianMinimum.slope (2 / 5)) (1 / 3) := by
    convert! coefficient_lower using 1
    norm_num [SignedGaussianMinimum.slope, parameter]
  have h := signed_kernel_lower (x₀ := 2 / 5) (beta := 1 / 3) (K := -5)
    (by norm_num) (by norm_num) (by norm_num) hK hy hx
  norm_num at h
  nlinarith

theorem tight_envelope {y x : ℝ} (hy : 1 / 3 ≤ y) (hx : 0 ≤ x) :
    exp (-(2 / 5 : ℝ)) * ((27 / 25 : ℝ) + (29 / 50) * (y - 1) - (11 / 5) * y * x) -
      (4813 / 1000) * (y - 1) ^ 2 ≤ y ^ (-(3 / 2 : ℝ)) * (1 - 2 * x) * exp (-x) := by
  have hK : (-(4813 / 1000) : ℝ) ≤ coefficient (SignedGaussianMinimum.slope (2 / 5)) (1 / 3) := by
    convert! tight_coefficient_lower using 1
    norm_num [SignedGaussianMinimum.slope, parameter]
  have h := signed_kernel_lower (x₀ := 2 / 5) (beta := 1 / 3) (K := -(4813 / 1000))
    (by norm_num) (by norm_num) (by norm_num) hK hy hx
  norm_num at h
  nlinarith

#print axioms cutoff_slope
#print axioms coefficient_lower
#print axioms envelope
#print axioms tight_envelope
end ForestUnimodality.SignedGaussian900
