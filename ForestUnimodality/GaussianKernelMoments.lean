import ForestUnimodality.TriangularGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-! Full-line Gaussian moments with the Fourier normalization, and the
integrated triangular-kernel variance-matching error. -/
namespace ForestUnimodality.GaussianKernelMoments
open Set Real MeasureTheory
open scoped Nat

theorem integrable_evenMoment {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ (2 * n) * Real.exp (-b * t ^ 2)) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq hb (s := ((2 * n : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  simpa only [Real.rpow_natCast] using hi

theorem integral_evenMoment {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∫ t : ℝ, t ^ (2 * n) * Real.exp (-b * t ^ 2)) =
      ((2 * n - 1 : ℕ)‼ : ℝ) * Real.sqrt Real.pi /
        ((2 : ℝ) ^ n * b ^ n * Real.sqrt b) := by
  have hhalf := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ))
    (q := ((2 * n : ℕ) : ℝ)) (b := b) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) hb
  simp only [Real.rpow_natCast, Real.rpow_two] at hhalf
  have he : -(((2 * n : ℕ) : ℝ) + 1) / 2 = -((n : ℝ) + 1 / 2) := by push_cast; ring
  have hg : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have hfull : (∫ t : ℝ, t ^ (2 * n) * Real.exp (-b * t ^ 2)) =
      2 * ∫ t : ℝ in Ioi 0, t ^ (2 * n) * Real.exp (-b * t ^ 2) := by
    have h := integral_comp_abs (f := fun t : ℝ => t ^ (2 * n) * Real.exp (-b * t ^ 2))
    simpa only [pow_mul, sq_abs] using h
  rw [hfull, hhalf, he, hg, Real.Gamma_nat_add_half, Real.rpow_neg hb.le,
    Real.rpow_add hb, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  ring

theorem integral_evenMoment_fourier {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, t ^ (2 * n) * Real.exp (-a * t ^ 2 / 2)) =
      ((2 * n - 1 : ℕ)‼ : ℝ) /
        (Real.sqrt (2 * Real.pi) * a ^ n * Real.sqrt a) := by
  have he : (fun t : ℝ => t ^ (2 * n) * Real.exp (-a * t ^ 2 / 2)) =
      (fun t : ℝ => t ^ (2 * n) * Real.exp (-(a / 2) * t ^ 2)) := by
    funext t
    congr 2
    ring
  rw [he, integral_evenMoment (by positivity : 0 < a / 2),
    Real.sqrt_div ha.le, div_pow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have htwo : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [ne_of_gt ha, hsa, hsp, hs2, ne_of_gt Real.pi_pos]
  nlinarith

theorem integral_second_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, t ^ 2 * Real.exp (-a * t ^ 2 / 2)) =
      1 / (Real.sqrt (2 * Real.pi) * a * Real.sqrt a) := by
  simpa using integral_evenMoment_fourier ha 1

theorem integral_fourth_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, t ^ 4 * Real.exp (-a * t ^ 2 / 2)) =
      3 / (Real.sqrt (2 * Real.pi) * a ^ 2 * Real.sqrt a) := by
  simpa [Nat.doubleFactorial] using integral_evenMoment_fourier ha 2

theorem integral_sixth_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, t ^ 6 * Real.exp (-a * t ^ 2 / 2)) =
      15 / (Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) := by
  simpa [Nat.doubleFactorial] using integral_evenMoment_fourier ha 3

/-- Absolute odd moments supply the cubic Bernoulli-error costs. -/
theorem integral_absOddMoment_fourier {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, |t| ^ (2 * n + 1) * Real.exp (-a * t ^ 2 / 2)) =
      (2 : ℝ) ^ n * (n.factorial : ℝ) / (Real.pi * a ^ (n + 1)) := by
  have hb : 0 < a / 2 := by positivity
  have hhalf := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ))
    (q := ((2 * n + 1 : ℕ) : ℝ)) (b := a / 2) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) hb
  simp only [Real.rpow_natCast, Real.rpow_two] at hhalf
  have he : -(((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hg : (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 := by push_cast; ring
  have hfull : (∫ t : ℝ, |t| ^ (2 * n + 1) * Real.exp (-a * t ^ 2 / 2)) =
      2 * ∫ t : ℝ in Ioi 0, t ^ (2 * n + 1) * Real.exp (-(a / 2) * t ^ 2) := by
    have h := integral_comp_abs (f := fun t : ℝ => t ^ (2 * n + 1) * Real.exp (-(a / 2) * t ^ 2))
    have heq : (fun t : ℝ => |t| ^ (2 * n + 1) * Real.exp (-a * t ^ 2 / 2)) =
        (fun t : ℝ => |t| ^ (2 * n + 1) * Real.exp (-(a / 2) * |t| ^ 2)) := by
      funext t
      rw [sq_abs]
      congr 2
      ring
    rw [heq]
    exact h
  rw [hfull, hhalf, he, hg, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb.le,
    Real.rpow_natCast, div_pow, pow_succ (2 : ℝ)]
  field_simp [ne_of_gt ha, ne_of_gt Real.pi_pos]

theorem integral_absCubic_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, |t| ^ 3 * Real.exp (-a * t ^ 2 / 2)) =
      2 / (Real.pi * a ^ 2) := by
  simpa using integral_absOddMoment_fourier ha 1

theorem integral_absFifth_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, |t| ^ 5 * Real.exp (-a * t ^ 2 / 2)) =
      8 / (Real.pi * a ^ 3) := by
  convert integral_absOddMoment_fourier ha 2 using 1
  norm_num [Nat.factorial]

noncomputable def sixthErrorMajorant (a t : ℝ) : ℝ :=
  t ^ 6 / 1440 * Real.exp (-a * t ^ 2 / 2)

theorem sixthErrorMajorant_nonneg (a t : ℝ) : 0 ≤ sixthErrorMajorant a t := by
  unfold sixthErrorMajorant
  positivity

theorem integrable_sixthErrorMajorant {a : ℝ} (ha : 0 < a) :
    Integrable (sixthErrorMajorant a) := by
  have hi := (integrable_evenMoment (by positivity : 0 < a / 2) 3).div_const 1440
  convert hi using 1
  funext t
  dsimp [sixthErrorMajorant]
  have he : -(a / 2) * t ^ 2 = -a * t ^ 2 / 2 := by ring
  rw [he]
  ring

theorem integral_sixthErrorMajorant_fourier {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ, sixthErrorMajorant a t) =
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) := by
  have he : sixthErrorMajorant a =
      fun t => (1 / 1440) * (t ^ 6 * Real.exp (-a * t ^ 2 / 2)) := by
    funext t
    unfold sixthErrorMajorant
    ring
  rw [he, integral_const_mul]
  calc
    _ = ((2 * Real.pi)⁻¹ * ∫ t : ℝ, t ^ 6 * Real.exp (-a * t ^ 2 / 2)) / 1440 := by ring
    _ = _ := by rw [integral_sixth_fourier ha]; ring

/-- An actual pointwise sixth-moment majorant controls a finite-period
complex Fourier integral with its exact normalization. -/
theorem norm_periodFourier_le_sixth {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : Continuous f)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖f t‖ ≤ sixthErrorMajorant a t) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t in -Real.pi..Real.pi, f t‖ ≤
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) := by
  have horder : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hm : (∫ t in -Real.pi..Real.pi, ‖f t‖) ≤
      ∫ t in -Real.pi..Real.pi, sixthErrorMajorant a t :=
    intervalIntegral.integral_mono_on horder (hf.norm.intervalIntegrable _ _)
      ((show Continuous (sixthErrorMajorant a) by unfold sixthErrorMajorant; fun_prop).intervalIntegrable _ _)
      hbound
  have hfull : (∫ t in -Real.pi..Real.pi, sixthErrorMajorant a t) ≤
      ∫ t : ℝ, sixthErrorMajorant a t := by
    rw [intervalIntegral.integral_of_le horder]
    exact setIntegral_le_integral (integrable_sixthErrorMajorant ha)
      (Filter.Eventually.of_forall (sixthErrorMajorant_nonneg a))
  have hn : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [norm_mul, hn, ← integral_sixthErrorMajorant_fourier ha]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (intervalIntegral.norm_integral_le_integral_norm horder).trans (hm.trans hfull)

/-- The newly proved triangular-kernel error, with any real frequency
shift, costs at most the exact `1/96` physical curvature budget. -/
theorem triangular_error_fourier_bound {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t in -Real.pi..Real.pi,
      Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I) *
        ((t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
          t ^ 2 * TriangularGaussian.kernel t * Real.exp (-a * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) := by
  apply norm_periodFourier_le_sixth ha
  · unfold TriangularGaussian.kernel
    fun_prop
  · intro t ht
    have hb := TriangularGaussian.variance_matched_error_bounds a (abs_le.mpr ht)
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im,
      zero_mul, sub_self, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hb.1]
    exact hb.2

theorem triangular_error_fourier_bound_rpow {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t in -Real.pi..Real.pi,
      Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I) *
        ((t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
          t ^ 2 * TriangularGaussian.kernel t * Real.exp (-a * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ (7 / 2 : ℝ)) := by
  have he : a ^ (7 / 2 : ℝ) = a ^ 3 * Real.sqrt a := by
    rw [show (7 / 2 : ℝ) = (3 : ℕ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add ha, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [he, ← mul_assoc]
  exact triangular_error_fourier_bound ha d

#print axioms integral_evenMoment
#print axioms integral_evenMoment_fourier
#print axioms integral_sixth_fourier
#print axioms integral_absOddMoment_fourier
#print axioms norm_periodFourier_le_sixth
#print axioms triangular_error_fourier_bound_rpow
end ForestUnimodality.GaussianKernelMoments
