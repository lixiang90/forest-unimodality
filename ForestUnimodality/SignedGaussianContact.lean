import ForestUnimodality.SignedGaussianGlobal

/-! Exact source contact parameters for the genuine signed Gaussian
profile. No numerical approximation of the optimizer is assumed. -/
namespace ForestUnimodality.SignedGaussianContact
open Set Real SignedGaussianMinimum SignedGaussianProfile SignedGaussianHermite

theorem contact_parameter {x₀ : ℝ} (hx : x₀ ∈ Ioo (0 : ℝ) (3 / 2)) :
    0 < SignedGaussianMinimum.slope x₀ ∧ SignedGaussianMinimum.slope x₀ < 3 := by
  exact ⟨mul_pos (by linarith [hx.2]) (exp_pos _), slope_lt_three hx.1⟩

theorem contact_arg {x₀ : ℝ} (hx : x₀ ∈ Ioo (0 : ℝ) (3 / 2)) :
    arg (SignedGaussianMinimum.slope x₀) 1 = x₀ := by
  simpa [arg] using point_slope hx

theorem contact_profile {x₀ : ℝ} (hx : x₀ ∈ Ioo (0 : ℝ) (3 / 2)) :
    profile (SignedGaussianMinimum.slope x₀) 1 = (1 + x₀ - 2 * x₀ ^ 2) * exp (-x₀) := by
  unfold profile
  rw [contact_arg hx]
  simp only [objective, one_rpow, one_mul, mul_one, SignedGaussianMinimum.slope]
  ring

theorem contact_first {x₀ : ℝ} (hx : x₀ ∈ Ioo (0 : ℝ) (3 / 2)) :
    first (SignedGaussianMinimum.slope x₀) 1 = (-(3 / 2 : ℝ) + 6 * x₀ - 2 * x₀ ^ 2) * exp (-x₀) := by
  unfold first
  rw [contact_arg hx]
  simp only [one_rpow, mul_one, SignedGaussianMinimum.slope]
  ring

theorem source_900_contact :
    SignedGaussianMinimum.slope (2 / 5) = (11 / 5 : ℝ) * exp (-(2 / 5 : ℝ)) ∧
    profile ((11 / 5 : ℝ) * exp (-(2 / 5 : ℝ))) 1 = (27 / 25 : ℝ) * exp (-(2 / 5 : ℝ)) ∧
    first ((11 / 5 : ℝ) * exp (-(2 / 5 : ℝ))) 1 = (29 / 50 : ℝ) * exp (-(2 / 5 : ℝ)) := by
  have hp := contact_profile (x₀ := 2 / 5) (by norm_num)
  have hf := contact_first (x₀ := 2 / 5) (by norm_num)
  norm_num [SignedGaussianMinimum.slope] at hp hf ⊢
  exact ⟨hp, hf⟩

theorem source_350_contact :
    SignedGaussianMinimum.slope (9 / 20) = (21 / 10 : ℝ) * exp (-(9 / 20 : ℝ)) ∧
    profile ((21 / 10 : ℝ) * exp (-(9 / 20 : ℝ))) 1 = (209 / 200 : ℝ) * exp (-(9 / 20 : ℝ)) ∧
    first ((21 / 10 : ℝ) * exp (-(9 / 20 : ℝ))) 1 = (159 / 200 : ℝ) * exp (-(9 / 20 : ℝ)) := by
  have hp := contact_profile (x₀ := 9 / 20) (by norm_num)
  have hf := contact_first (x₀ := 9 / 20) (by norm_num)
  norm_num [SignedGaussianMinimum.slope] at hp hf ⊢
  exact ⟨hp, hf⟩

theorem coefficient_eq_quotient {c beta : ℝ}
    (hc : 0 < c) (hc3 : c < 3) (hb : 0 < beta) (hb1 : beta < 1) :
    coefficient c beta =
      (profile c beta - profile c 1 - first c 1 * (beta - 1)) / (1 - beta) ^ 2 := by
  have he := coefficient_identity hc hb
    (show (1 : ℝ) ∈ Icc beta 1 from ⟨hb1.le, le_rfl⟩)
    (by simpa using hc3) (show beta ∈ Icc beta 1 from ⟨le_rfl, hb1.le⟩)
  apply (eq_div_iff (pow_ne_zero 2 (by linarith : 1 - beta ≠ 0))).mpr
  nlinarith

theorem signed_kernel_lower {x₀ beta K y x : ℝ}
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) (3 / 2)) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hK : K ≤ coefficient (SignedGaussianMinimum.slope x₀) beta) (hby : beta ≤ y) (hx : 0 ≤ x) :
    exp (-x₀) * ((1 + x₀ - 2 * x₀ ^ 2) + (-(3 / 2 : ℝ) + 6 * x₀ - 2 * x₀ ^ 2) * (y - 1) -
      (3 - 2 * x₀) * y * x) + K * (y - 1) ^ 2 ≤
        y ^ (-(3 / 2 : ℝ)) * (1 - 2 * x) * exp (-x) := by
  have hc := contact_parameter hx₀
  have h := SignedGaussianGlobal.objective_lower hc.1 hc.2 hb hb1 hK hby hx
  unfold quadratic at h
  rw [contact_profile hx₀, contact_first hx₀] at h
  unfold objective SignedGaussianMinimum.slope at h
  nlinarith

#print axioms source_900_contact
#print axioms source_350_contact
#print axioms coefficient_eq_quotient
#print axioms signed_kernel_lower
end ForestUnimodality.SignedGaussianContact
