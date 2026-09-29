import ForestUnimodality.BernoulliGaussian
import ForestUnimodality.GaussianCurvatureTail

/-! A full-period damping estimate at every nonnegative Bernoulli variance,
and a uniform first-difference bound for the actual integer-indexed masses. -/
namespace ForestUnimodality
open Real Set MeasureTheory

theorem centeredBernoulliCharacteristic_norm_le_periodGaussian {q t : ℝ}
    (hv : 0 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t‖ ≤
      Real.exp (-2 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) := by
  have hc := Real.cos_le_one_sub_mul_cos_sq ht
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * (q * (1 - q)) by positivity)
  have he := Real.add_one_le_exp (-4 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2)
  have hsq : ‖centeredBernoulliCharacteristic q t‖ ^ 2 ≤
      Real.exp (-4 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) := by
    rw [centeredBernoulliCharacteristic_norm_sq]
    calc
      _ ≤ -4 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2 + 1 := by
        linear_combination hm
      _ ≤ _ := he
  have heq : Real.exp (-2 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) ^ 2 =
      Real.exp (-4 * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  rw [← heq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq

theorem centeredBernoulliCharacteristic_pow_norm_le_periodGaussian (m : ℕ) {q t : ℝ}
    (hv : 0 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t ^ m‖ ≤
      Real.exp (-2 * (m : ℝ) * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) := by
  rw [norm_pow]
  have he := pow_le_pow_left₀ (norm_nonneg _)
    (centeredBernoulliCharacteristic_norm_le_periodGaussian hv ht) m
  rw [← Real.exp_nat_mul] at he
  convert he using 1
  congr 1
  ring_nf

theorem binomialCharacteristic_norm_le_periodGaussian (m : ℕ) {q t : ℝ}
    (hv : 0 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖binomialCharacteristic m q t‖ ≤
      Real.exp (-2 * (m : ℝ) * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) := by
  have he := centeredBernoulliCharacteristic_pow_norm_le_periodGaussian m hv ht
  simpa only [norm_pow, centeredBernoulliCharacteristic_norm, binomialCharacteristic] using he

namespace BinomialGradientBound

noncomputable def multiplier (t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) * Complex.I)) - 1

theorem norm_multiplier_le (t : ℝ) : ‖multiplier t‖ ≤ |t| := by
  have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -t)
  simpa [multiplier, mul_comm, Real.norm_eq_abs] using he

theorem gradient_eq_periodFourier (m : ℕ) (j : ℤ) (q : ℝ) :
    ((binomialMass m (j + 1) q - binomialMass m j q : ℝ) : ℂ) =
      periodFourier (fun t => multiplier t * binomialCharacteristic m q t) j := by
  have hc := continuous_binomialCharacteristic m q
  have hf : (fun t => multiplier t * binomialCharacteristic m q t) =
      (fun t : ℝ => Complex.exp (((-1 : ℤ) : ℂ) * t * Complex.I) *
        binomialCharacteristic m q t - binomialCharacteristic m q t) := by
    funext t
    simp [multiplier, sub_mul]
  rw [hf, periodFourier_sub _ _ (by fun_prop) hc, periodFourier_shift]
  push_cast
  simp only [sub_neg_eq_add, binomialMass_eq_periodFourier]

theorem norm_periodFourier_le_firstMoment {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi,
      ‖f t‖ ≤ |t| * Real.exp (-a * t ^ 2 / 2)) (j : ℤ) :
    ‖periodFourier f j‖ ≤ 1 / (Real.pi * a) := by
  let g : ℝ → ℝ := fun t => |t| * Real.exp (-a * t ^ 2 / 2)
  have hig : Integrable g := by
    have hi := (GaussianCurvatureTail.integrable_real_moment ha 1).norm
    simpa only [pow_one, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hi
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg0 (t : ℝ) : 0 ≤ g t := by dsimp [g]; positivity
  have horder : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hphase (t : ℝ) : ‖Complex.exp (-((j : ℂ) * t * Complex.I)) * f t‖ = ‖f t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hfinite : (∫ t in -Real.pi..Real.pi,
      ‖Complex.exp (-((j : ℂ) * t * Complex.I)) * f t‖) ≤
      ∫ t in -Real.pi..Real.pi, g t := by
    simp_rw [hphase]
    exact intervalIntegral.integral_mono_on horder (hf.norm.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) hbound
  have hfull : (∫ t in -Real.pi..Real.pi, g t) ≤ ∫ t : ℝ, g t := by
    rw [intervalIntegral.integral_of_le horder]
    exact setIntegral_le_integral hig (Filter.Eventually.of_forall hg0)
  have hn : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]
  have hmajor : ‖periodFourier f j‖ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, g t := by
    rw [periodFourier, norm_mul, hn]
    exact mul_le_mul_of_nonneg_left
      ((intervalIntegral.norm_integral_le_integral_norm horder).trans (hfinite.trans hfull))
      (by positivity)
  refine hmajor.trans_eq ?_
  simpa [g] using GaussianKernelMoments.integral_absOddMoment_fourier ha 0

/-- This bound uses no near-symmetry restriction. Integer indices outside the
binomial support are included by the exact Fourier coefficient identity. -/
theorem binomial_gradient_bound (m : ℕ) (hm : 0 < m) (j : ℤ) {q : ℝ}
    (hv : 0 < q * (1 - q)) :
    |binomialMass m (j + 1) q - binomialMass m j q| ≤
      Real.pi / (4 * (m : ℝ) * (q * (1 - q))) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ha : 0 < 4 * (m : ℝ) * (q * (1 - q)) / Real.pi ^ 2 := by positivity
  have hc := continuous_binomialCharacteristic m q
  have hb := norm_periodFourier_le_firstMoment ha
    (f := fun t => multiplier t * binomialCharacteristic m q t)
    (by unfold multiplier; fun_prop) ?_ j
  · rw [← gradient_eq_periodFourier, Complex.norm_real, Real.norm_eq_abs] at hb
    convert hb using 1
    field_simp
  · intro t ht
    rw [norm_mul]
    calc
      _ ≤ |t| * Real.exp (-2 * (m : ℝ) * (q * (1 - q)) * t ^ 2 / Real.pi ^ 2) :=
        mul_le_mul (norm_multiplier_le t)
          (binomialCharacteristic_norm_le_periodGaussian m hv.le (abs_le.mpr ht))
          (norm_nonneg _) (abs_nonneg _)
      _ = _ := by congr 2; ring_nf

#print axioms binomial_gradient_bound
#print axioms gradient_eq_periodFourier
#print axioms centeredBernoulliCharacteristic_pow_norm_le_periodGaussian
end BinomialGradientBound
end ForestUnimodality
