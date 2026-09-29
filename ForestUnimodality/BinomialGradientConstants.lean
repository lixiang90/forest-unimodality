import ForestUnimodality.BinomialGradientEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fixed finite gradient constants certified by exact rational comparisons. -/
namespace ForestUnimodality.BinomialGradientConstants
open Real BinomialGradientEnvelope

noncomputable def piLower : ℝ := 31415 / 10000
noncomputable def eLower : ℝ := 27182818283 / 10000000000

structure Valid (s η qlo c : ℝ) : Prop where
  positive : 0 < s
  eta_nonneg : 0 ≤ η
  qlo_pos : 0 < qlo
  c_nonneg : 0 ≤ c
  stirling_denom : 1 < 24 * s ^ 2
  interior : X s < 4 * qlo * s
  variance : 0 < R s η
  square : K s η / (2 * piLower * eLower * R s η) *
    (24 * s ^ 2 / (24 * s ^ 2 - 1)) ≤ c ^ 2

theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  apply (le_div_iff₀ (sub_pos.mpr hx)).mpr
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add] at he
  norm_num at he
  nlinarith

theorem stirling_exp_budget {D s : ℝ} (_hD : 0 < D) (hs : 0 < s)
    (hDs : 4 * s ^ 2 ≤ D) (hd : 1 < 24 * s ^ 2) :
    Real.exp (1 / (6 * D)) ≤ 24 * s ^ 2 / (24 * s ^ 2 - 1) := by
  have hcmp : (1 : ℝ) / (6 * D) ≤ 1 / (24 * s ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hsmall : (1 : ℝ) / (24 * s ^ 2) < 1 := (div_lt_one (by positivity)).mpr hd
  calc
    _ ≤ Real.exp (1 / (24 * s ^ 2)) := Real.exp_le_exp.mpr hcmp
    _ ≤ 1 / (1 - 1 / (24 * s ^ 2)) := exp_le_inv_one_sub hsmall
    _ = _ := by field_simp

theorem true_square_le_rational {s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η)
    (hR : 0 < R s η) (hd : 1 < 24 * s ^ 2) :
    K s η / (2 * Real.pi * Real.exp 1 * R s η) * (24 * s ^ 2 / (24 * s ^ 2 - 1)) ≤
      K s η / (2 * piLower * eLower * R s η) * (24 * s ^ 2 / (24 * s ^ 2 - 1)) := by
  have hpi : piLower ≤ Real.pi := by convert! Real.pi_gt_d4.le using 1; norm_num [piLower]
  have he : eLower ≤ Real.exp 1 := by convert! Real.exp_one_gt_d9.le using 1; norm_num [eLower]
  have hpl : 0 < piLower := by norm_num [piLower]
  have hel : 0 < eLower := by norm_num [eLower]
  have hK : 0 < K s η := by unfold K; have := X_pos hs; positivity
  have hden : 2 * piLower * eLower * R s η ≤ 2 * Real.pi * Real.exp 1 * R s η := by
    gcongr
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hK.le (by positivity) hden) (by positivity)

theorem weightedDeviation_bound (n : ℕ) {q s η qlo c : ℝ} (h : Valid s η qlo c)
    (hq0 : qlo ≤ q) (hq1 : q ≤ 1 - qlo) (heta : |1 - 2 * q| ≤ η)
    (hvar : s ^ 2 ≤ (n : ℝ) * (q * (1 - q))) (j : ℤ) :
    |(n : ℝ) * q - j| * binomialMass n j q ≤ c := by
  have hs := h.positive
  have hη := h.eta_nonneg
  have hR := h.variance
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := ⟨h.qlo_pos.trans_le hq0, by linarith [h.qlo_pos]⟩
  have hv : 0 < q * (1 - q) := mul_pos hq.1 (sub_pos.mpr hq.2)
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    rw [hn0] at hvar
    norm_num at hvar
    nlinarith [sq_pos_of_pos h.positive]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hDs : 4 * s ^ 2 ≤ (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hv1 hnR.le]
  obtain ⟨k, hk, hmax⟩ := BinomialGradientMaximum.exists_maximum n q
  have hsq := maximum_weightedDeviation_sq_bound n k hn hk h.positive h.eta_nonneg
    h.qlo_pos hq0 hq1 heta hvar h.interior h.variance hmax
  have hK : 0 < K s η := by unfold K; have := X_pos h.positive; positivity
  have hbudget : K s η / (2 * Real.pi * R s η) * Real.exp (1 / (6 * n) - 1) ≤ c ^ 2 := by
    rw [Real.exp_sub]
    calc
      _ ≤ K s η / (2 * Real.pi * R s η) *
          ((24 * s ^ 2 / (24 * s ^ 2 - 1)) / Real.exp 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (stirling_exp_budget hnR h.positive hDs h.stirling_denom)
            (Real.exp_pos _).le) (by positivity)
      _ = K s η / (2 * Real.pi * Real.exp 1 * R s η) *
          (24 * s ^ 2 / (24 * s ^ 2 - 1)) := by ring
      _ ≤ _ := (true_square_le_rational h.positive h.eta_nonneg h.variance h.stirling_denom).trans h.square
  have hkmass0 := binomialMass_nonneg n k hq.1.le hq.2.le
  have hk0 : 0 ≤ BinomialGradientMaximum.weightedDeviation n q k := by
    dsimp [BinomialGradientMaximum.weightedDeviation]
    exact mul_nonneg (abs_nonneg _) hkmass0
  have hkc := (sq_le_sq₀ hk0 h.c_nonneg).mp (hsq.trans hbudget)
  by_cases hj0 : 0 ≤ j
  · by_cases hjn : j ≤ n
    · lift j to ℕ using hj0
      have hle : j ≤ n := by exact_mod_cast hjn
      simpa only [BinomialGradientMaximum.weightedDeviation, Int.cast_natCast] using (hmax j hle).trans hkc
    · rw [binomialMass_eq_zero_of_gt n (lt_of_not_ge hjn), mul_zero]
      exact h.c_nonneg
  · rw [binomialMass_eq_zero_of_neg n (lt_of_not_ge hj0), mul_zero]
    exact h.c_nonneg

theorem gradient_bound (d : ℕ) (j : ℤ) {q s η qlo c : ℝ} (h : Valid s η qlo c)
    (hq0 : qlo ≤ q) (hq1 : q ≤ 1 - qlo) (heta : |1 - 2 * q| ≤ η)
    (hvar : s ^ 2 ≤ ((d + 1 : ℕ) : ℝ) * (q * (1 - q))) :
    |binomialMass d j q - binomialMass d (j - 1) q| ≤
      c / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := ⟨h.qlo_pos.trans_le hq0, by linarith [h.qlo_pos]⟩
  have hv : 0 < q * (1 - q) := mul_pos hq.1 (sub_pos.mpr hq.2)
  have hD : 0 < ((d + 1 : ℕ) : ℝ) * (q * (1 - q)) := by positivity
  rw [binomial_gradient_identity d j hv.ne', abs_mul, abs_div, abs_of_pos hD,
    abs_of_nonneg (binomialMass_nonneg (d + 1) j hq.1.le hq.2.le), div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (weightedDeviation_bound (d + 1) h hq0 hq1 heta hvar j) hD.le

#print axioms weightedDeviation_bound
#print axioms gradient_bound
end ForestUnimodality.BinomialGradientConstants
