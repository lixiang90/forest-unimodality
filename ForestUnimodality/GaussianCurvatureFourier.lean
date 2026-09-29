import ForestUnimodality.GaussianKernelMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Exact full-line Fourier transform of Gaussian curvature, obtained from
the Gaussian integral and two integrable derivatives. -/
namespace ForestUnimodality.GaussianCurvatureFourier
open Real Complex MeasureTheory

noncomputable def phase (s d t : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * (t : ℂ) ^ 2 / 2 - (d : ℂ) * t * Complex.I)

theorem norm_phase (s d t : ℝ) : ‖phase s d t‖ = Real.exp (-s * t ^ 2 / 2) := by
  rw [phase, Complex.norm_exp]
  simp [pow_two]

theorem continuous_phase (s d : ℝ) : Continuous (phase s d) := by
  unfold phase
  fun_prop

theorem phase_eq (s d t : ℝ) : phase s d t =
    Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I) * (Real.exp (-s * t ^ 2 / 2) : ℂ) := by
  unfold phase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_moment {s : ℝ} (hs : 0 < s) (d : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ n * phase s d t) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < s / 2)
    (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
  simp only [Real.rpow_natCast] at hi
  refine ⟨(by unfold phase; fun_prop : Continuous (fun t : ℝ =>
    (t : ℂ) ^ n * phase s d t)).aestronglyMeasurable, ?_⟩
  have hh := hi.hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at hh ⊢
  convert hh using 1
  funext t
  rw [norm_mul, norm_pow, norm_phase, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

theorem hasDerivAt_phase (s d t : ℝ) :
    HasDerivAt (phase s d) ((-(s : ℂ) * t - (d : ℂ) * Complex.I) * phase s d t) t := by
  have hd : HasDerivAt (fun x : ℂ => Complex.exp (-(s : ℂ) * x ^ 2 / 2 - (d : ℂ) * x * Complex.I))
      ((-(s : ℂ) * t - (d : ℂ) * Complex.I) * phase s d t) (t : ℂ) := by
    convert! (((((hasDerivAt_id (t : ℂ)).pow 2).const_mul (-(s : ℂ))).div_const 2).sub
      (((hasDerivAt_id (t : ℂ)).const_mul (d : ℂ)).mul_const Complex.I)).cexp using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, phase,
      Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  exact hd.comp_ofReal

theorem integral_phase {s : ℝ} (hs : 0 < s) (d : ℝ) :
    (∫ t : ℝ, phase s d t) =
      ((Real.sqrt (2 * Real.pi / s) * Real.exp (-d ^ 2 / (2 * s)) : ℝ) : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have he := integral_cexp_quadratic (b := -(s : ℂ) / 2) (by simp; linarith)
    (-(d : ℂ) * Complex.I) 0
  have hfun : phase s d = fun t : ℝ =>
      Complex.exp ((-(s : ℂ) / 2) * (t : ℂ) ^ 2 + (-(d : ℂ) * Complex.I) * t + 0) := by
    funext t
    unfold phase
    congr 1
    ring
  rw [hfun, he]
  have hbase : (Real.pi : ℂ) / (-(-(s : ℂ) / 2)) = ((2 * Real.pi / s : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hexp : (0 : ℂ) - (-(d : ℂ) * Complex.I) ^ 2 / (4 * (-(s : ℂ) / 2)) =
      ((-d ^ 2 / (2 * s) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    field_simp
    ring
  rw [hbase, hexp]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, ← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi / s),
    ← Real.sqrt_eq_rpow, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

theorem first_moment_relation {s : ℝ} (hs : 0 < s) (d : ℝ) :
    -(s : ℂ) * (∫ t : ℝ, (t : ℂ) * phase s d t) -
      (d : ℂ) * Complex.I * (∫ t : ℝ, phase s d t) = 0 := by
  have h0 : Integrable (phase s d) := by simpa using integrable_moment hs d 0
  have h1 : Integrable (fun t : ℝ => (t : ℂ) * phase s d t) := by
    simpa using integrable_moment hs d 1
  have hi : Integrable (fun t : ℝ =>
      (-(s : ℂ) * t - (d : ℂ) * Complex.I) * phase s d t) := by
    convert (h1.const_mul (-(s : ℂ))).sub (h0.const_mul ((d : ℂ) * Complex.I)) using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  have he := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_phase s d) hi h0
  have hf : (fun t : ℝ => (-(s : ℂ) * t - (d : ℂ) * Complex.I) * phase s d t) =
      (fun t : ℝ => -(s : ℂ) * ((t : ℂ) * phase s d t) - (d : ℂ) * Complex.I * phase s d t) := by
    funext t
    ring
  rw [hf, integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul] at he
  exact he

theorem second_moment_relation {s : ℝ} (hs : 0 < s) (d : ℝ) :
    (∫ t : ℝ, phase s d t) - (s : ℂ) * (∫ t : ℝ, (t : ℂ) ^ 2 * phase s d t) -
      (d : ℂ) * Complex.I * (∫ t : ℝ, (t : ℂ) * phase s d t) = 0 := by
  have h0 : Integrable (phase s d) := by simpa using integrable_moment hs d 0
  have h1 : Integrable (fun t : ℝ => (t : ℂ) * phase s d t) := by
    simpa using integrable_moment hs d 1
  have h2 := integrable_moment hs d 2
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) * phase s d t)
      (phase s d t - (s : ℂ) * ((t : ℂ) ^ 2 * phase s d t) -
        (d : ℂ) * Complex.I * ((t : ℂ) * phase s d t)) t := by
    convert! ((hasDerivAt_id (t : ℂ)).comp_ofReal.mul (hasDerivAt_phase s d t)) using 1
    simp only [one_mul, id_eq]
    ring
  have hi := (h0.sub (h2.const_mul (s : ℂ))).sub (h1.const_mul ((d : ℂ) * Complex.I))
  have he := integral_eq_zero_of_hasDerivAt_of_integrable hd hi h1
  have hsub0 := integral_sub h0 (h2.const_mul (s : ℂ))
  have hsub1 := integral_sub (h0.sub (h2.const_mul (s : ℂ)))
    (h1.const_mul ((d : ℂ) * Complex.I))
  simp only [Pi.sub_apply] at hsub0 hsub1
  rw [hsub1, hsub0, integral_const_mul, integral_const_mul] at he
  exact he

theorem integral_second_moment {s : ℝ} (hs : 0 < s) (d : ℝ) :
    (∫ t : ℝ, (t : ℂ) ^ 2 * phase s d t) =
      (((1 - d ^ 2 / s) / s * Real.sqrt (2 * Real.pi / s) *
        Real.exp (-d ^ 2 / (2 * s)) : ℝ) : ℂ) := by
  have h1 := first_moment_relation hs d
  have h2 := second_moment_relation hs d
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcomb := congrArg₂ (fun a b : ℂ => (s : ℂ) * a - (d : ℂ) * Complex.I * b) h2 h1
  simp only [mul_zero, sub_zero] at hcomb
  have halg (A B C : ℂ) : (s : ℂ) * (A - (s : ℂ) * C - (d : ℂ) * Complex.I * B) -
      (d : ℂ) * Complex.I * (-(s : ℂ) * B - (d : ℂ) * Complex.I * A) =
      ((s : ℂ) - (d : ℂ) ^ 2) * A - (s : ℂ) ^ 2 * C := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [halg] at hcomb
  have he : (∫ t : ℝ, (t : ℂ) ^ 2 * phase s d t) =
      (((s : ℂ) - (d : ℂ) ^ 2) / (s : ℂ) ^ 2) * (∫ t : ℝ, phase s d t) := by
    field_simp
    linear_combination -hcomb
  rw [he, integral_phase hs d]
  push_cast
  field_simp

noncomputable def curvature (s d : ℝ) : ℝ :=
  (1 - d ^ 2 / s) / (Real.sqrt (2 * Real.pi) * s * Real.sqrt s) *
    Real.exp (-d ^ 2 / (2 * s))

/-- Exact physical Gaussian curvature with Fourier normalization. -/
theorem integral_curvature_fourier {s : ℝ} (hs : 0 < s) (d : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, (t : ℂ) ^ 2 * phase s d t) =
      (curvature s d : ℂ) := by
  rw [integral_second_moment hs d]
  have hreal : (2 * Real.pi)⁻¹ *
      ((1 - d ^ 2 / s) / s * Real.sqrt (2 * Real.pi / s) * Real.exp (-d ^ 2 / (2 * s))) =
      curvature s d := by
    unfold curvature
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
    have hr : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hp : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hs' : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
    field_simp [hp, hs', hs.ne', Real.pi_ne_zero]
    nlinarith
  exact_mod_cast hreal

#print axioms integral_phase
#print axioms first_moment_relation
#print axioms second_moment_relation
#print axioms integral_curvature_fourier
end ForestUnimodality.GaussianCurvatureFourier
