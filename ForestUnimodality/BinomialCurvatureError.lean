import ForestUnimodality.BernoulliGaussianError
import ForestUnimodality.GaussianCurvatureTail

/-! Finite physical curvature-error budget for actual binomial masses. -/
namespace ForestUnimodality.BinomialCurvatureError
open Real Set MeasureTheory

noncomputable def periodIntegral (f : ℝ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t in -Real.pi..Real.pi, f t

theorem periodIntegral_sub (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    periodIntegral (fun t => f t - g t) = periodIntegral f - periodIntegral g := by
  unfold periodIntegral
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_sub]

noncomputable def oscillation (d t : ℝ) : ℂ :=
  Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I)

theorem norm_oscillation (d t : ℝ) : ‖oscillation d t‖ = 1 := by
  unfold oscillation
  rw [Complex.norm_exp]
  simp

theorem norm_periodIntegral_le_moments {b c₃ c₄ : ℝ} (hb : 0 < b)
    (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) {f : ℝ → ℂ} (hf : Continuous f)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖f t‖ ≤
      c₃ * (|t| ^ 5 * Real.exp (-b * t ^ 2 / 2)) +
        c₄ * (t ^ 6 * Real.exp (-b * t ^ 2 / 2))) :
    ‖periodIntegral f‖ ≤ c₃ * (8 / (Real.pi * b ^ 3)) +
      c₄ * (15 / (Real.sqrt (2 * Real.pi) * b ^ 3 * Real.sqrt b)) := by
  have hi5 : Integrable (fun t : ℝ => |t| ^ 5 * Real.exp (-b * t ^ 2 / 2)) := by
    have hi := (GaussianCurvatureTail.integrable_real_moment hb 5).norm
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using hi
  have hi6 := GaussianCurvatureTail.integrable_real_moment hb 6
  let g : ℝ → ℝ := fun t => c₃ * (|t| ^ 5 * Real.exp (-b * t ^ 2 / 2)) +
    c₄ * (t ^ 6 * Real.exp (-b * t ^ 2 / 2))
  have hig : Integrable g := (hi5.const_mul c₃).add (hi6.const_mul c₄)
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg0 (t : ℝ) : 0 ≤ g t := by dsimp [g]; positivity
  have horder : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfinite : (∫ t in -Real.pi..Real.pi, ‖f t‖) ≤ ∫ t in -Real.pi..Real.pi, g t :=
    intervalIntegral.integral_mono_on horder (hf.norm.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) hbound
  have hfull : (∫ t in -Real.pi..Real.pi, g t) ≤ ∫ t : ℝ, g t := by
    rw [intervalIntegral.integral_of_le horder]
    exact setIntegral_le_integral hig (Filter.Eventually.of_forall hg0)
  have hn : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]
  have hmajor : ‖periodIntegral f‖ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, g t := by
    rw [periodIntegral, norm_mul, hn]
    exact mul_le_mul_of_nonneg_left
      ((intervalIntegral.norm_integral_le_integral_norm horder).trans (hfinite.trans hfull)) (by positivity)
  refine hmajor.trans_eq ?_
  rw [show g = (fun t => c₃ * (|t| ^ 5 * Real.exp (-b * t ^ 2 / 2)) +
    c₄ * (t ^ 6 * Real.exp (-b * t ^ 2 / 2))) from rfl,
    integral_add (hi5.const_mul _) (hi6.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ = c₃ * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, |t| ^ 5 * Real.exp (-b * t ^ 2 / 2)) +
        c₄ * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, t ^ 6 * Real.exp (-b * t ^ 2 / 2)) := by ring_nf
    _ = _ := by rw [GaussianKernelMoments.integral_absFifth_fourier hb,
      GaussianKernelMoments.integral_sixth_fourier hb]

noncomputable def bernoulliErrorIntegrand (m : ℕ) (q d t : ℝ) : ℂ :=
  oscillation d t * (t ^ 2 * TriangularGaussian.kernel t : ℝ) *
    (centeredBernoulliCharacteristic q t ^ m -
      (Real.exp (-(m : ℝ) * (q * (1 - q)) * t ^ 2 / 2) : ℂ))

theorem bernoulli_error_fourier_bound (m : ℕ) (hm : 2 ≤ m) {q : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (d : ℝ) :
    ‖periodIntegral (bernoulliErrorIntegrand m q d)‖ ≤
      4 * (m : ℝ) * (q * (1 - q)) * |1 - 2 * q| /
        (3 * Real.pi * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 3) +
      5 * (m : ℝ) * (q * (1 - q)) /
        (16 * Real.sqrt (2 * Real.pi) * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 3 *
          Real.sqrt (((m - 1 : ℕ) : ℝ) * (q * (1 - q)))) := by
  have hv0 : 0 < q * (1 - q) := by linarith
  have hm0 : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hb : 0 < ((m - 1 : ℕ) : ℝ) * (q * (1 - q)) := mul_pos hm0 hv0
  have he := norm_periodIntegral_le_moments hb
    (c₃ := (m : ℝ) * (q * (1 - q)) * |1 - 2 * q| / 6)
    (c₄ := (m : ℝ) * (q * (1 - q)) / 48) (by positivity) (by positivity)
    (f := bernoulliErrorIntegrand m q d)
    (by unfold bernoulliErrorIntegrand oscillation centeredBernoulliCharacteristic TriangularGaussian.kernel; fun_prop) ?_
  · generalize hbdef : ((m - 1 : ℕ) : ℝ) * (q * (1 - q)) = b at hb he ⊢
    have hsqrt : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
    convert he using 1
    field_simp [hb.ne', hsqrt, Real.pi_ne_zero]
    ring_nf
  · intro t ht
    have ht' : |t| ≤ Real.pi := abs_le.mpr ht
    have herr := centeredBinomialCharacteristic_error_bound m hv ht'
    have hk0 := TriangularGaussian.kernel_nonneg t
    have hk1 := TriangularGaussian.kernel_le_one t
    have hfactor : 0 ≤ t ^ 2 * TriangularGaussian.kernel t := mul_nonneg (sq_nonneg t) hk0
    have hfactorle : t ^ 2 * TriangularGaussian.kernel t ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    rw [bernoulliErrorIntegrand, norm_mul, norm_mul, norm_oscillation, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor]
    calc
      _ ≤ t ^ 2 * ((m : ℝ) *
          (q * (1 - q) * |1 - 2 * q| * |t| ^ 3 / 6 + q * (1 - q) * t ^ 4 / 48) *
          Real.exp (-((m - 1 : ℕ) : ℝ) * (q * (1 - q)) * t ^ 2 / 2)) :=
        mul_le_mul hfactorle herr (norm_nonneg _) (sq_nonneg t)
      _ = _ := by
        rw [show t ^ 4 = (t ^ 2) ^ 2 by ring_nf, show t ^ 6 = (t ^ 2) ^ 3 by ring_nf, ← sq_abs t]
        ring_nf

noncomputable def actualCurvatureIntegrand (m : ℕ) (q d t : ℝ) : ℂ :=
  oscillation d t * (t ^ 2 * TriangularGaussian.kernel t : ℝ) *
    centeredBernoulliCharacteristic q t ^ m

noncomputable def latticeGaussianIntegrand (a d t : ℝ) : ℂ :=
  oscillation d t * (t ^ 2 * TriangularGaussian.kernel t * Real.exp (-a * t ^ 2 / 2) : ℝ)

noncomputable def gaussianCurvatureIntegrand (a d t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 * GaussianCurvatureFourier.phase a d t

theorem binomial_curvature_eq_periodIntegral (m : ℕ) (j : ℤ) (q : ℝ) :
    ((2 * binomialMass m j q - binomialMass m (j - 1) q - binomialMass m (j + 1) q : ℝ) : ℂ) =
      periodIntegral (actualCurvatureIntegrand m q ((j : ℝ) - m * q)) := by
  rw [binomial_curvature_eq_centered_integral, periodIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  unfold actualCurvatureIntegrand oscillation
  have hl : (t ^ 2 * TriangularGaussian.kernel t : ℝ) = 2 - 2 * Real.cos t :=
    TriangularGaussian.lattice_identity t
  rw [hl]
  push_cast
  have hp : -(((j : ℝ) - (m : ℝ) * q : ℝ) : ℂ) * t * Complex.I =
      -((((j : ℝ) - m * q) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring_nf
  push_cast at hp
  rw [hp]
  ring_nf

theorem bernoulli_period_difference_bound (m : ℕ) (hm : 2 ≤ m) {q : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (d : ℝ) :
    ‖periodIntegral (actualCurvatureIntegrand m q d) -
      periodIntegral (latticeGaussianIntegrand ((m : ℝ) * (q * (1 - q))) d)‖ ≤
      4 * (m : ℝ) * (q * (1 - q)) * |1 - 2 * q| /
        (3 * Real.pi * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 3) +
      5 * (m : ℝ) * (q * (1 - q)) /
        (16 * Real.sqrt (2 * Real.pi) * (((m - 1 : ℕ) : ℝ) * (q * (1 - q))) ^ 3 *
          Real.sqrt (((m - 1 : ℕ) : ℝ) * (q * (1 - q)))) := by
  rw [← periodIntegral_sub _ _
    (by unfold actualCurvatureIntegrand oscillation centeredBernoulliCharacteristic TriangularGaussian.kernel; fun_prop)
    (by unfold latticeGaussianIntegrand oscillation TriangularGaussian.kernel; fun_prop)]
  have he : (fun t => actualCurvatureIntegrand m q d t -
      latticeGaussianIntegrand ((m : ℝ) * (q * (1 - q))) d t) = bernoulliErrorIntegrand m q d := by
    funext t
    unfold actualCurvatureIntegrand latticeGaussianIntegrand bernoulliErrorIntegrand
    push_cast
    have hx : -((m : ℝ) * (q * (1 - q))) * t ^ 2 / 2 =
        -(m : ℝ) * (q * (1 - q)) * t ^ 2 / 2 := by ring_nf
    have hxC := congrArg (fun x : ℝ => (x : ℂ)) hx
    push_cast at hxC
    rw [hxC]
    ring_nf
  rw [he]
  exact bernoulli_error_fourier_bound m hm hv d

theorem triangular_period_difference_bound {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ‖periodIntegral (latticeGaussianIntegrand a d) -
      periodIntegral (gaussianCurvatureIntegrand (a + 1 / 6) d)‖ ≤
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) := by
  rw [norm_sub_rev, ← periodIntegral_sub _ _
    (by unfold gaussianCurvatureIntegrand GaussianCurvatureFourier.phase; fun_prop)
    (by unfold latticeGaussianIntegrand oscillation TriangularGaussian.kernel; fun_prop)]
  have he : (fun t => gaussianCurvatureIntegrand (a + 1 / 6) d t - latticeGaussianIntegrand a d t) =
      (fun t => Complex.exp (-((d * t : ℝ) : ℂ) * Complex.I) *
        ((t ^ 2 * Real.exp (-(a + 1 / 6) * t ^ 2 / 2) -
          t ^ 2 * TriangularGaussian.kernel t * Real.exp (-a * t ^ 2 / 2) : ℝ) : ℂ)) := by
    funext t
    unfold gaussianCurvatureIntegrand latticeGaussianIntegrand oscillation
    rw [GaussianCurvatureFourier.phase_eq]
    push_cast
    ring_nf
  rw [he]
  exact GaussianKernelMoments.triangular_error_fourier_bound ha d

theorem gaussian_period_difference_bound {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ‖periodIntegral (gaussianCurvatureIntegrand (a + 1 / 6) d) -
      (GaussianCurvatureFourier.curvature (a + 1 / 6) d : ℂ)‖ ≤
      (1 / a + 1 / (Real.pi ^ 2 * a ^ 2)) * Real.exp (-a * Real.pi ^ 2 / 2) := by
  have hs : 0 < a + 1 / 6 := by linarith
  rw [norm_sub_rev, ← GaussianCurvatureFourier.integral_curvature_fourier hs d]
  unfold periodIntegral gaussianCurvatureIntegrand
  rw [← mul_sub]
  exact GaussianCurvatureTail.norm_full_sub_period_le ha (by linarith) d

/-- Actual binomial curvature versus the variance-matched Gaussian. These
four finite costs are the two Bernoulli errors, the triangular-kernel error,
and the Gaussian tail outside the original period. -/
theorem binomial_curvature_error_bound_raw (m : ℕ) (hm : 2 ≤ m) (j : ℤ) {q : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) :
    let v := q * (1 - q)
    let a := (m : ℝ) * v
    let b := ((m - 1 : ℕ) : ℝ) * v
    |2 * binomialMass m j q - binomialMass m (j - 1) q - binomialMass m (j + 1) q -
      GaussianCurvatureFourier.curvature (a + 1 / 6) ((j : ℝ) - m * q)| ≤
      (4 * (m : ℝ) * v * |1 - 2 * q| / (3 * Real.pi * b ^ 3) +
        5 * (m : ℝ) * v / (16 * Real.sqrt (2 * Real.pi) * b ^ 3 * Real.sqrt b)) +
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ 3 * Real.sqrt a) +
      (1 / a + 1 / (Real.pi ^ 2 * a ^ 2)) * Real.exp (-a * Real.pi ^ 2 / 2) := by
  dsimp only
  have hv0 : 0 < q * (1 - q) := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 < (m : ℝ) * (q * (1 - q)) := mul_pos hm0 hv0
  let d : ℝ := (j : ℝ) - m * q
  let A := periodIntegral (actualCurvatureIntegrand m q d)
  let B := periodIntegral (latticeGaussianIntegrand ((m : ℝ) * (q * (1 - q))) d)
  let C := periodIntegral (gaussianCurvatureIntegrand ((m : ℝ) * (q * (1 - q)) + 1 / 6) d)
  let D : ℂ := GaussianCurvatureFourier.curvature ((m : ℝ) * (q * (1 - q)) + 1 / 6) d
  have hreal : |2 * binomialMass m j q - binomialMass m (j - 1) q - binomialMass m (j + 1) q -
      GaussianCurvatureFourier.curvature ((m : ℝ) * (q * (1 - q)) + 1 / 6) d| = ‖A - D‖ := by
    dsimp [A, D]
    rw [← binomial_curvature_eq_periodIntegral]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hreal]
  calc
    _ ≤ ‖A - B‖ + ‖B - D‖ := norm_sub_le_norm_sub_add_norm_sub A B D
    _ ≤ (‖A - B‖ + ‖B - C‖) + ‖C - D‖ := by
      have he := norm_sub_le_norm_sub_add_norm_sub B C D
      linarith
    _ ≤ _ := add_le_add
      (add_le_add (bernoulli_period_difference_bound m hm hv d) (triangular_period_difference_bound ha d))
      (gaussian_period_difference_bound ha d)

private theorem rpow_seven_halves {x : ℝ} (hx : 0 < x) :
    x ^ (7 / 2 : ℝ) = x ^ 3 * Real.sqrt x := by
  rw [show (7 / 2 : ℝ) = (3 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private theorem rpow_five_halves {x : ℝ} (hx : 0 < x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private theorem first_cost_eq_source {x y v : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv : 0 < v) (η : ℝ) :
    4 * x * v * η / (3 * Real.pi * (y * v) ^ 3) =
      4 * η * (x / y) ^ 3 / (3 * Real.pi * v ^ 2 * x ^ 2) := by
  field_simp

private theorem second_cost_eq_source {x y v : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv : 0 < v) :
    5 * x * v / (16 * Real.sqrt (2 * Real.pi) * (y * v) ^ 3 * Real.sqrt (y * v)) =
      5 * (x / y) ^ (7 / 2 : ℝ) /
        (16 * Real.sqrt (2 * Real.pi) * (x * v) ^ (5 / 2 : ℝ)) := by
  rw [rpow_seven_halves (div_pos hx hy), rpow_five_halves (mul_pos hx hv),
    Real.sqrt_div hx.le, Real.sqrt_mul hy.le, Real.sqrt_mul hx.le, div_pow, mul_pow, mul_pow]
  have hxS : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hyS : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hvS : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  field_simp [hx.ne', hy.ne', hv.ne', hxS, hyS, hvS]

/-- Stage 350 (4.5), in its original rho and real-power notation. -/
theorem binomial_curvature_error_bound (m : ℕ) (hm : 2 ≤ m) (j : ℤ) {q : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) :
    let v := q * (1 - q)
    let a := (m : ℝ) * v
    let ρ := (m : ℝ) / ((m : ℝ) - 1)
    |2 * binomialMass m j q - binomialMass m (j - 1) q - binomialMass m (j + 1) q -
      GaussianCurvatureFourier.curvature (a + 1 / 6) ((j : ℝ) - m * q)| ≤
      (4 * |1 - 2 * q| * ρ ^ 3 / (3 * Real.pi * v ^ 2 * (m : ℝ) ^ 2) +
        5 * ρ ^ (7 / 2 : ℝ) / (16 * Real.sqrt (2 * Real.pi) * a ^ (5 / 2 : ℝ))) +
      1 / (96 * Real.sqrt (2 * Real.pi) * a ^ (7 / 2 : ℝ)) +
      (1 / a + 1 / (Real.pi ^ 2 * a ^ 2)) * Real.exp (-a * Real.pi ^ 2 / 2) := by
  have hraw := binomial_curvature_error_bound_raw m hm j hv
  dsimp only at hraw ⊢
  have hv0 : 0 < q * (1 - q) := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [first_cost_eq_source hm0 hn0 hv0, second_cost_eq_source hm0 hn0 hv0, hsub] at hraw
  rw [rpow_seven_halves (mul_pos hm0 hv0)]
  simpa only [mul_assoc] using hraw

#print axioms norm_periodIntegral_le_moments
#print axioms bernoulli_error_fourier_bound
#print axioms binomial_curvature_error_bound_raw
#print axioms binomial_curvature_error_bound
end ForestUnimodality.BinomialCurvatureError
