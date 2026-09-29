import ForestUnimodality.SignedGaussian900
import ForestUnimodality.GaussianDirectionalLayerBudget
import ForestUnimodality.GaussianCurvatureFourier

/-! The stage-900 signed Gaussian main term under the actual hard-core
layer law, with the exact 4813/1000 variance price. The variance is Mv;
no triangular-noise shift or independence of M and the layer mean is used. -/
namespace ForestUnimodality.SignedGaussianLayerBudget
open Real NegativePowerLayerBudget GaussianDirectionalLayerBudget

noncomputable def kernel (y w : ℝ) : ℝ :=
  y ^ (-(3 / 2 : ℝ)) * (1 - w ^ 2 / y) * exp (-(w ^ 2 / (2 * y)))
noncomputable def polynomial (y w : ℝ) : ℝ :=
  exp (-(2 / 5 : ℝ)) * ((27 / 25 : ℝ) + (29 / 50) * (y - 1) - (11 / 10) * w ^ 2) -
    (4813 / 1000) * (y - 1) ^ 2

theorem polynomial_le_kernel {y w : ℝ} (hy : 1 / 3 ≤ y) : polynomial y w ≤ kernel y w := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have h := SignedGaussian900.tight_envelope hy
    (div_nonneg (sq_nonneg w) (mul_pos (by norm_num : (0 : ℝ) < 2) hy0).le)
  have he : y * (w ^ 2 / (2 * y)) = w ^ 2 / 2 := by field_simp
  have he' : 2 * (w ^ 2 / (2 * y)) = w ^ 2 / y := by ring
  rw [he'] at h
  rw [mul_assoc (11 / 5 : ℝ) y _, he] at h
  unfold polynomial kernel
  nlinarith [h]

theorem polynomial_nonpos {y w : ℝ} (hy : y ≤ 1 / 3) : polynomial y w ≤ 0 := by
  have he0 := exp_pos (-(2 / 5 : ℝ))
  have he1 : exp (-(2 / 5 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  have hl : (27 / 25 : ℝ) + (29 / 50) * (y - 1) ≤ 52 / 75 := by linarith
  have hm := mul_le_mul_of_nonneg_left hl he0.le
  have hb := mul_le_mul_of_nonneg_right he1 (by norm_num : (0 : ℝ) ≤ 52 / 75)
  have hs : (4 / 9 : ℝ) ≤ (y - 1) ^ 2 := by nlinarith
  have hw := mul_nonneg he0.le (sq_nonneg w)
  unfold polynomial
  nlinarith

theorem kernel_eq_scaled_curvature {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (d : ℝ) :
    kernel (s / a) (d / sqrt a) =
      (sqrt (2 * Real.pi) * a * sqrt a) * GaussianCurvatureFourier.curvature s d := by
  have hsa : 0 < s / a := div_pos hs ha
  have hsq : 0 < sqrt a := sqrt_pos.2 ha
  have hss : 0 < sqrt s := sqrt_pos.2 hs
  have hp : 0 < sqrt (2 * Real.pi) := sqrt_pos.2 (by positivity)
  have hpow : (s / a) ^ (-(3 / 2 : ℝ)) = a * sqrt a / (s * sqrt s) := by
    rw [rpow_neg hsa.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add hsa, rpow_one, ← sqrt_eq_rpow, sqrt_div hs.le]
    field_simp
  have hratio : (d / sqrt a) ^ 2 / (s / a) = d ^ 2 / s := by
    rw [div_pow, sq_sqrt ha.le]
    field_simp
  have hex : (d / sqrt a) ^ 2 / (2 * (s / a)) = d ^ 2 / (2 * s) := by
    rw [div_pow, sq_sqrt ha.le]
    field_simp
  unfold kernel GaussianCurvatureFourier.curvature
  rw [hpow, hratio, hex, neg_div]
  field_simp

variable {V : Type*} [DecidableEq V]

theorem polynomial_expectation (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k v : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hv : 0 < v) :
    hardCoreLayerExpectation G S I z (fun j M => polynomial ((M : ℝ) / m)
      ((k - binomialLayerMean j M z) / sqrt (v * m))) =
      exp (-(2 / 5 : ℝ)) * (27 / 25 - (11 / 10) *
        ((hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m) / (v * m))) -
        (4813 / 1000) * (hardCoreAvailableVariance G S I z / m ^ 2) := by
  have hmeanM : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ)) = m := by
    simpa only [hardCoreLayerExpectation, hardCoreAvailableMean] using hm.symm
  have hy : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) / m - 1) = 0 := by
    have he : (fun (_ : ℕ) (M : ℕ) => (M : ℝ) / m - 1) =
        (fun (_ : ℕ) (M : ℕ) => (1 / m) * (M : ℝ) - 1) := by funext j M; ring
    rw [he, layer_sub, layer_const_mul, hmeanM, layer_const G S I hIS hI hz.le]
    field_simp
    ring
  have hpoint (y w : ℝ) : polynomial y w =
      GaussianDirectionalEnvelope.quadratic (exp (-(2 / 5 : ℝ)) * (27 / 25))
        (exp (-(2 / 5 : ℝ)) * (11 / 10)) (4813 / 1000) 0 y w +
        (exp (-(2 / 5 : ℝ)) * (29 / 50) + 1 / 2) * (y - 1) := by
    unfold polynomial GaussianDirectionalEnvelope.quadratic
    ring
  simp_rw [hpoint]
  rw [layer_add, layer_const_mul, hy, mul_zero, add_zero,
    quadratic_expectation G S I hIS hI hz hm hm0 hmean hv]
  ring

theorem actual_normalized_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k v R D : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hv : 0 < v)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (v * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m) :
    exp (-(2 / 5 : ℝ)) * (27 / 25 - (11 / 10) * R) - (4813 / 1000) * D / m ≤
      hardCoreLayerExpectation G S I z (fun j M => if m / 3 ≤ (M : ℝ) then
        kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / sqrt (v * m)) else 0) := by
  have hp (j M : ℕ) : polynomial ((M : ℝ) / m)
      ((k - binomialLayerMean j M z) / sqrt (v * m)) ≤
      if m / 3 ≤ (M : ℝ) then
        kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / sqrt (v * m)) else 0 := by
    by_cases hg : m / 3 ≤ (M : ℝ)
    · rw [if_pos hg]
      exact polynomial_le_kernel ((le_div_iff₀ hm0).mpr (by nlinarith))
    · rw [if_neg hg]
      exact polynomial_nonpos ((div_le_iff₀ hm0).mpr (by nlinarith [le_of_not_ge hg]))
  have hraw := layer_mono G S I hz.le _ _ hp
  rw [polynomial_expectation G S I hIS hI hz hm hm0 hmean hv] at hraw
  have hL := (div_le_iff₀ (mul_pos hv hm0)).mpr hvarL
  have hM : hardCoreAvailableVariance G S I z / m ^ 2 ≤ D / m := by
    calc
      _ ≤ (D * m) / m ^ 2 := div_le_div_of_nonneg_right hvarM (sq_nonneg m)
      _ = _ := by field_simp
  have hl := mul_le_mul_of_nonneg_left hL (exp_pos (-(2 / 5 : ℝ))).le
  have hM' := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 4813 / 1000)
  rw [mul_div_assoc]
  nlinarith

theorem actual_scaled_curvature_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k v R D : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hv : 0 < v)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (v * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m) :
    exp (-(2 / 5 : ℝ)) * (27 / 25 - (11 / 10) * R) - (4813 / 1000) * D / m ≤
      (sqrt (2 * Real.pi) * (v * m) * sqrt (v * m)) *
        hardCoreLayerExpectation G S I z (fun j M => if m / 3 ≤ (M : ℝ) then
          GaussianCurvatureFourier.curvature (v * M) (k - binomialLayerMean j M z) else 0) := by
  have h := actual_normalized_lower G S I hIS hI hz hm hm0 hmean hv hvarL hvarM
  have he (j M : ℕ) : (if m / 3 ≤ (M : ℝ) then
      kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / sqrt (v * m)) else 0) =
      (sqrt (2 * Real.pi) * (v * m) * sqrt (v * m)) *
        (if m / 3 ≤ (M : ℝ) then GaussianCurvatureFourier.curvature (v * M)
          (k - binomialLayerMean j M z) else 0) := by
    by_cases hg : m / 3 ≤ (M : ℝ)
    · rw [if_pos hg, if_pos hg]
      have hM : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity : 0 < m / 3) hg
      have hr : (v * (M : ℝ)) / (v * m) = (M : ℝ) / m := by field_simp
      rw [← hr, kernel_eq_scaled_curvature (mul_pos hv hm0) (mul_pos hv hM)]
    · simp only [if_neg hg, mul_zero]
  simp_rw [he] at h
  rw [layer_const_mul] at h
  exact h

theorem actual_curvature_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k v R D : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hv : 0 < v)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (v * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m) :
    (exp (-(2 / 5 : ℝ)) * (27 / 25 - (11 / 10) * R) - (4813 / 1000) * D / m) /
        (sqrt (2 * Real.pi) * (v * m) * sqrt (v * m)) ≤
      hardCoreLayerExpectation G S I z (fun j M => if m / 3 ≤ (M : ℝ) then
        GaussianCurvatureFourier.curvature (v * M) (k - binomialLayerMean j M z) else 0) := by
  have hs : 0 < sqrt (2 * Real.pi) * (v * m) * sqrt (v * m) := by positivity
  apply (div_le_iff₀ hs).mpr
  simpa only [mul_comm] using
    actual_scaled_curvature_lower G S I hIS hI hz hm hm0 hmean hv hvarL hvarM

#print axioms polynomial_nonpos
#print axioms polynomial_expectation
#print axioms actual_normalized_lower
#print axioms kernel_eq_scaled_curvature
#print axioms actual_scaled_curvature_lower
#print axioms actual_curvature_lower
end ForestUnimodality.SignedGaussianLayerBudget
