import ForestUnimodality.BernoulliCutoff
import ForestUnimodality.GaussianCurvatureTail

/-! Finite-cutoff Fourier approximation of actual binomial point masses.
The true outer-frequency part and the full Gaussian tail are paid separately. -/
namespace ForestUnimodality.BinomialPointMassError
open Real Set MeasureTheory

noncomputable def cutoffIntegral (T : ℝ) (f : ℝ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t in -T..T, f t

theorem cutoffIntegral_sub (T : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    cutoffIntegral T (fun t => f t - g t) = cutoffIntegral T f - cutoffIntegral T g := by
  unfold cutoffIntegral
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_sub]

theorem norm_normalizer : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
  simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]

theorem norm_cutoff_le_moments {T b c₃ c₄ : ℝ} (hT : 0 ≤ T) (hb : 0 < b)
    (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) {f : ℝ → ℂ} (hf : Continuous f)
    (hbound : ∀ t ∈ Icc (-T) T, ‖f t‖ ≤
      c₃ * (|t| ^ 3 * Real.exp (-b * t ^ 2 / 2)) +
        c₄ * (t ^ 4 * Real.exp (-b * t ^ 2 / 2))) :
    ‖cutoffIntegral T f‖ ≤ c₃ * (2 / (Real.pi * b ^ 2)) +
      c₄ * (3 / (Real.sqrt (2 * Real.pi) * b ^ 2 * Real.sqrt b)) := by
  have hi3 : Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-b * t ^ 2 / 2)) := by
    have hi := (GaussianCurvatureTail.integrable_real_moment hb 3).norm
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using hi
  have hi4 := GaussianCurvatureTail.integrable_real_moment hb 4
  let g : ℝ → ℝ := fun t => c₃ * (|t| ^ 3 * Real.exp (-b * t ^ 2 / 2)) +
    c₄ * (t ^ 4 * Real.exp (-b * t ^ 2 / 2))
  have hig : Integrable g := (hi3.const_mul c₃).add (hi4.const_mul c₄)
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg0 (t : ℝ) : 0 ≤ g t := by dsimp [g]; positivity
  have horder : -T ≤ T := by linarith
  have hfinite : (∫ t in -T..T, ‖f t‖) ≤ ∫ t in -T..T, g t :=
    intervalIntegral.integral_mono_on horder (hf.norm.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) hbound
  have hfull : (∫ t in -T..T, g t) ≤ ∫ t : ℝ, g t := by
    rw [intervalIntegral.integral_of_le horder]
    exact setIntegral_le_integral hig (Filter.Eventually.of_forall hg0)
  have hmajor : ‖cutoffIntegral T f‖ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, g t := by
    rw [cutoffIntegral, norm_mul, norm_normalizer]
    exact mul_le_mul_of_nonneg_left
      ((intervalIntegral.norm_integral_le_integral_norm horder).trans (hfinite.trans hfull)) (by positivity)
  refine hmajor.trans_eq ?_
  rw [show g = (fun t => c₃ * (|t| ^ 3 * Real.exp (-b * t ^ 2 / 2)) +
    c₄ * (t ^ 4 * Real.exp (-b * t ^ 2 / 2))) from rfl,
    integral_add (hi3.const_mul _) (hi4.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ = c₃ * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, |t| ^ 3 * Real.exp (-b * t ^ 2 / 2)) +
        c₄ * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, t ^ 4 * Real.exp (-b * t ^ 2 / 2)) := by ring_nf
    _ = _ := by rw [GaussianKernelMoments.integral_absCubic_fourier hb,
      GaussianKernelMoments.integral_fourth_fourier hb]

theorem norm_interval_le_const {a b C : ℝ} (hab : a ≤ b) {f : ℝ → ℂ} (hf : Continuous f)
    (hbound : ∀ t ∈ Icc a b, ‖f t‖ ≤ C) :
    ‖∫ t in a..b, f t‖ ≤ (b - a) * C := by
  calc
    _ ≤ ∫ t in a..b, ‖f t‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _ in a..b, C := intervalIntegral.integral_mono_on hab
      (hf.norm.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hbound
    _ = _ := by simp

theorem norm_period_sub_cutoff {T C : ℝ} (hT : 0 ≤ T) (hTp : T ≤ Real.pi)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hbound : ∀ t, T ≤ |t| → |t| ≤ Real.pi → ‖f t‖ ≤ C) :
    ‖cutoffIntegral Real.pi f - cutoffIntegral T f‖ ≤ (1 - T / Real.pi) * C := by
  have hleft := norm_interval_le_const (show -Real.pi ≤ -T by linarith) hf
    (C := C) (by
      intro t ht
      have ht0 : t ≤ 0 := by linarith [ht.2]
      apply hbound t
      · rw [abs_of_nonpos ht0]; linarith [ht.2]
      · rw [abs_of_nonpos ht0]; linarith [ht.1])
  have hright := norm_interval_le_const hTp hf (C := C) (by
    intro t ht
    exact hbound t (by rw [abs_of_nonneg (hT.trans ht.1)]; exact ht.1)
      (by rw [abs_of_nonneg (hT.trans ht.1)]; exact ht.2))
  have hsplit : (∫ t in -Real.pi..Real.pi, f t) - (∫ t in -T..T, f t) =
      (∫ t in -Real.pi..-T, f t) + (∫ t in T..Real.pi, f t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-Real.pi) (-T)) (hf.intervalIntegrable (-T) T)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-Real.pi) T) (hf.intervalIntegrable T Real.pi)
    rw [← h2, ← h1]
    ring_nf
  rw [cutoffIntegral, cutoffIntegral, ← mul_sub, hsplit, norm_mul, norm_normalizer]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((-T - -Real.pi) * C + (Real.pi - T) * C) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hleft hright)) (by positivity)
    _ = _ := by field_simp; ring_nf

noncomputable def actualIntegrand (m : ℕ) (q d t : ℝ) : ℂ :=
  Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I) * centeredBernoulliCharacteristic q t ^ m

theorem norm_actualIntegrand (m : ℕ) (q d t : ℝ) :
    ‖actualIntegrand m q d t‖ = ‖centeredBernoulliCharacteristic q t ^ m‖ := by
  unfold actualIntegrand
  rw [norm_mul, Complex.norm_exp]
  simp

theorem binomialMass_eq_cutoff (m : ℕ) (j : ℤ) (q : ℝ) :
    (binomialMass m j q : ℂ) =
      cutoffIntegral Real.pi (actualIntegrand m q ((j : ℝ) - m * q)) := by
  rw [binomialMass_eq_periodFourier]
  unfold cutoffIntegral periodFourier
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simpa only [actualIntegrand, Complex.ofReal_mul, neg_mul] using centered_binomial_identity m j q t

theorem central_error_bound (m : ℕ) (hm : 2 ≤ m) {q T : ℝ}
    (h : BernoulliCutoff.Valid q T) (d : ℝ) :
    ‖cutoffIntegral T (actualIntegrand m q d) -
      cutoffIntegral T (GaussianCurvatureFourier.phase ((m : ℝ) * (q * (1 - q))) d)‖ ≤
      (m : ℝ) * (q * (1 - q)) * |1 - 2 * q| /
        (3 * Real.pi * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 2) +
      (m : ℝ) * (q * (1 - q)) /
        (16 * Real.sqrt (2 * Real.pi) * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 2 *
          Real.sqrt (((m - 1 : ℕ) : ℝ) * (q * (1 - q)))) := by
  have hv0 : 0 < q * (1 - q) := by linarith [h.variance]
  have hn0 : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hb := mul_pos hn0 hv0
  let f := fun t => actualIntegrand m q d t -
    GaussianCurvatureFourier.phase ((m : ℝ) * (q * (1 - q))) d t
  have hc : Continuous (actualIntegrand m q d) := by
    unfold actualIntegrand centeredBernoulliCharacteristic; fun_prop
  have hd := GaussianCurvatureFourier.continuous_phase ((m : ℝ) * (q * (1 - q))) d
  rw [← cutoffIntegral_sub T _ _ hc hd]
  have he := norm_cutoff_le_moments h.positive.le hb
    (c₃ := (m : ℝ) * (q * (1 - q)) * |1 - 2 * q| / 6)
    (c₄ := (m : ℝ) * (q * (1 - q)) / 48) (by positivity) (by positivity)
    (f := f) (hc.sub hd) ?_
  · convert he using 1
    field_simp
    ring_nf
  · intro t ht
    have herr := BernoulliCutoff.pow_error_bound m h (abs_le.mpr ht)
    dsimp [f, actualIntegrand]
    rw [GaussianCurvatureFourier.phase_eq, ← mul_sub, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im,
      zero_mul, sub_zero, Real.exp_zero, one_mul]
    convert herr using 1 <;> ring_nf

noncomputable def gaussianDensity (a d : ℝ) : ℝ :=
  Real.exp (-d ^ 2 / (2 * a)) / (Real.sqrt (2 * Real.pi) * Real.sqrt a)

theorem integral_gaussianDensity {a : ℝ} (ha : 0 < a) (d : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, GaussianCurvatureFourier.phase a d t) =
      (gaussianDensity a d : ℂ) := by
  rw [GaussianCurvatureFourier.integral_phase ha d]
  have hreal : (2 * Real.pi)⁻¹ *
      (Real.sqrt (2 * Real.pi / a) * Real.exp (-d ^ 2 / (2 * a))) = gaussianDensity a d := by
    unfold gaussianDensity
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
    have hr : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hp : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    field_simp [hp, hs, ha.ne', Real.pi_ne_zero]
    nlinarith
  exact_mod_cast hreal

theorem gaussian_zero_outside_eq {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ t : ℝ in (Ioc (-T) T)ᶜ, Real.exp (-a * t ^ 2 / 2)) =
      2 * ∫ t : ℝ in Ioi T, Real.exp (-a * t ^ 2 / 2) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2 / 2)) := by
    simpa using GaussianCurvatureTail.integrable_real_moment ha 0
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith))
    measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have he := integral_comp_neg_Iic (-T) (fun t : ℝ => Real.exp (-a * t ^ 2 / 2))
  simp only [neg_sq, neg_neg] at he
  rw [he]
  ring_nf

theorem gaussian_tail_bound {a T : ℝ} (ha : 0 < a) (hT : 0 < T) (d : ℝ) :
    ‖cutoffIntegral T (GaussianCurvatureFourier.phase a d) - (gaussianDensity a d : ℂ)‖ ≤
      Real.exp (-a * T ^ 2 / 2) / (Real.pi * a * T) := by
  have hi : Integrable (GaussianCurvatureFourier.phase a d) := by
    simpa using GaussianCurvatureFourier.integrable_moment ha d 0
  have hd : (∫ t : ℝ, GaussianCurvatureFourier.phase a d t) -
      (∫ t in -T..T, GaussianCurvatureFourier.phase a d t) =
      ∫ t : ℝ in (Ioc (-T) T)ᶜ, GaussianCurvatureFourier.phase a d t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_compl measurableSet_Ioc hi).symm
  rw [← integral_gaussianDensity ha d, norm_sub_rev, cutoffIntegral, ← mul_sub, hd,
    norm_mul, norm_normalizer]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ in (Ioc (-T) T)ᶜ,
        ‖GaussianCurvatureFourier.phase a d t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (2 * Real.pi)⁻¹ * (2 * ∫ t : ℝ in Ioi T, Real.exp (-a * t ^ 2 / 2)) := by
      simp_rw [GaussianCurvatureFourier.norm_phase]
      rw [gaussian_zero_outside_eq ha hT.le]
    _ ≤ (2 * Real.pi)⁻¹ * (2 * (Real.exp (-a * T ^ 2 / 2) / (a * T))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (GaussianCurvatureTail.integral_zero_tail_le ha hT)
          (by norm_num)) (by positivity)
    _ = _ := by field_simp

theorem actual_tail_bound (m : ℕ) {q T : ℝ} (h : BernoulliCutoff.Valid q T) (d : ℝ) :
    ‖cutoffIntegral Real.pi (actualIntegrand m q d) -
      cutoffIntegral T (actualIntegrand m q d)‖ ≤
      (1 - T / Real.pi) * Real.exp (-(m : ℝ) * (q * (1 - q)) * T ^ 2 / 2) := by
  apply norm_period_sub_cutoff h.positive.le h.period.le
    (by unfold actualIntegrand centeredBernoulliCharacteristic; fun_prop)
  intro t htT ht
  rw [norm_actualIntegrand]
  exact BernoulliCutoff.pow_norm_outside m h htT ht

/-- The complete finite point-mass estimate, including both distinct tails.
No normal approximation of the original lattice law is used as an assumption. -/
theorem binomial_pointMass_error_bound_raw (m : ℕ) (hm : 2 ≤ m) (j : ℤ) {q T : ℝ}
    (h : BernoulliCutoff.Valid q T) :
    let a := (m : ℝ) * (q * (1 - q))
    let b := ((m - 1 : ℕ) : ℝ) * (q * (1 - q))
    |binomialMass m j q - gaussianDensity a ((j : ℝ) - m * q)| ≤
      ((m : ℝ) * (q * (1 - q)) * |1 - 2 * q| / (3 * Real.pi * b ^ 2) +
        (m : ℝ) * (q * (1 - q)) / (16 * Real.sqrt (2 * Real.pi) * b ^ 2 * Real.sqrt b)) +
      (1 - T / Real.pi) * Real.exp (-a * T ^ 2 / 2) +
      Real.exp (-a * T ^ 2 / 2) / (Real.pi * a * T) := by
  dsimp only
  have hv0 : 0 < q * (1 - q) := by linarith [h.variance]
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc := central_error_bound m hm h ((j : ℝ) - m * q)
  have ht := actual_tail_bound m h ((j : ℝ) - m * q)
  have hg := gaussian_tail_bound (mul_pos hm0 hv0) h.positive ((j : ℝ) - m * q)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (cutoffIntegral Real.pi (actualIntegrand m q ((j : ℝ) - m * q)))
    (cutoffIntegral T (actualIntegrand m q ((j : ℝ) - m * q)))
    (gaussianDensity ((m : ℝ) * (q * (1 - q))) ((j : ℝ) - m * q) : ℂ)
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    (cutoffIntegral T (actualIntegrand m q ((j : ℝ) - m * q)))
    (cutoffIntegral T (GaussianCurvatureFourier.phase ((m : ℝ) * (q * (1 - q)))
      ((j : ℝ) - m * q)))
    (gaussianDensity ((m : ℝ) * (q * (1 - q))) ((j : ℝ) - m * q) : ℂ)
  rw [← binomialMass_eq_cutoff] at htri
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
  rw [← binomialMass_eq_cutoff] at ht
  simp only [neg_mul] at ht hg ⊢
  linarith

private theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = (1 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, pow_one, ← Real.sqrt_eq_rpow]

private theorem rpow_five_halves {x : ℝ} (hx : 0 < x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private theorem first_cost_eq_source {x y v : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv : 0 < v) (η : ℝ) :
    x * v * η / (3 * Real.pi * (y * v) ^ 2) =
      η * (x / y) ^ 2 / (3 * Real.pi * (x * v)) := by
  field_simp

private theorem second_cost_eq_source {x y v : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv : 0 < v) :
    x * v / (16 * Real.sqrt (2 * Real.pi) * (y * v) ^ 2 * Real.sqrt (y * v)) =
      (x / y) ^ (5 / 2 : ℝ) / (16 * Real.sqrt (2 * Real.pi) * (x * v) ^ (3 / 2 : ℝ)) := by
  rw [rpow_five_halves (div_pos hx hy), rpow_three_halves (mul_pos hx hv),
    Real.sqrt_div hx.le, Real.sqrt_mul hy.le, Real.sqrt_mul hx.le, div_pow, mul_pow]
  have hxS : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hyS : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hvS : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  field_simp [hx.ne', hy.ne', hv.ne', hxS, hyS, hvS]

/-- Stage 900 (6.4), with `a = Mv` and `rho = M/(M-1)`. -/
theorem binomial_pointMass_error_bound (m : ℕ) (hm : 2 ≤ m) (j : ℤ) {q T : ℝ}
    (h : BernoulliCutoff.Valid q T) :
    let a := (m : ℝ) * (q * (1 - q))
    let ρ := (m : ℝ) / ((m : ℝ) - 1)
    |binomialMass m j q - gaussianDensity a ((j : ℝ) - m * q)| ≤
      (|1 - 2 * q| * ρ ^ 2 / (3 * Real.pi * a) +
        ρ ^ (5 / 2 : ℝ) / (16 * Real.sqrt (2 * Real.pi) * a ^ (3 / 2 : ℝ))) +
      (1 - T / Real.pi) * Real.exp (-a * T ^ 2 / 2) +
      Real.exp (-a * T ^ 2 / 2) / (Real.pi * a * T) := by
  have he := binomial_pointMass_error_bound_raw m hm j h
  dsimp only at he ⊢
  have hv0 : 0 < q * (1 - q) := by linarith [h.variance]
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [first_cost_eq_source hm0 hn0 hv0, second_cost_eq_source hm0 hn0 hv0, hsub] at he
  exact he

#print axioms central_error_bound
#print axioms norm_period_sub_cutoff
#print axioms gaussian_tail_bound
#print axioms binomial_pointMass_error_bound_raw
#print axioms binomial_pointMass_error_bound
end ForestUnimodality.BinomialPointMassError
