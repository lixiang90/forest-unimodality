import ForestUnimodality.GaussianDirectionalEnvelope
import ForestUnimodality.NegativePowerLayerBudget

/-! Averaging of the real directional quadratic on the same actual layer
law. Both linear terms vanish by genuine mean identities, even when the
free count and the conditional mean are correlated. -/
namespace ForestUnimodality.GaussianDirectionalLayerBudget

open GaussianDirectionalEnvelope NegativePowerLayerBudget

variable {V : Type*} [DecidableEq V]

theorem quadratic_expectation (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k nu : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (H a B theta : ℝ) :
    hardCoreLayerExpectation G S I z (fun j M => quadratic H a B theta
      ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m))) =
      H - a * ((hardCoreVariance G S z -
        (z / (1 + z)) * (1 - z / (1 + z)) * m) / (nu * m)) -
        B * (hardCoreAvailableVariance G S I z / m ^ 2) := by
  have hmeanM : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ)) = m := by
    simpa only [hardCoreLayerExpectation, hardCoreAvailableMean] using hm.symm
  have hy : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) / m - 1) = 0 := by
    have he : (fun (_ : ℕ) (M : ℕ) => (M : ℝ) / m - 1) =
        (fun (_ : ℕ) (M : ℕ) => (1 / m) * (M : ℝ) - 1) := by funext j M; ring
    rw [he, layer_sub, layer_const_mul, hmeanM, layer_const G S I hIS hI hz.le]
    field_simp
    ring
  have hx : hardCoreLayerExpectation G S I z
      (fun j M => (k - binomialLayerMean j M z) / Real.sqrt (nu * m)) = 0 := by
    have he : (fun j M => (k - binomialLayerMean j M z) / Real.sqrt (nu * m)) =
        (fun j M => (1 / Real.sqrt (nu * m)) * (k - binomialLayerMean j M z)) := by
      funext j M; ring
    rw [he, layer_const_mul, hardCoreLayerExpectation_centered_mean G S I hIS hI hz hmean, mul_zero]
  have hy2 : hardCoreLayerExpectation G S I z (fun _ M => ((M : ℝ) / m - 1) ^ 2) =
      hardCoreAvailableVariance G S I z / m ^ 2 := by
    have he (M : ℕ) : ((M : ℝ) / m - 1) ^ 2 = (1 / m ^ 2) * ((M : ℝ) - m) ^ 2 := by
      field_simp
    simp_rw [he]
    rw [layer_const_mul, hm]
    change (1 / _) * hardCoreAvailableVariance G S I z = _
    ring
  have hx2 : hardCoreLayerExpectation G S I z
      (fun j M => ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2) =
      (hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m) / (nu * m) := by
    have he (j M : ℕ) : ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2 =
        (1 / (nu * m)) * (k - binomialLayerMean j M z) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (mul_pos hnu hm0).le]
      ring
    simp_rw [he]
    rw [layer_const_mul, hardCoreLayerExpectation_centered_sq G S I hIS hI hz hmean, hm]
    ring
  have hq (j M : ℕ) : quadratic H a B theta ((M : ℝ) / m)
      ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) =
      H - (1 / 2) * ((M : ℝ) / m - 1) -
        theta * ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) -
        a * (((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2) -
        B * (((M : ℝ) / m - 1) ^ 2) := by unfold quadratic; ring
  simp_rw [hq]
  rw [layer_sub, layer_sub, layer_sub, layer_sub,
    layer_const G S I hIS hI hz.le, layer_const_mul, layer_const_mul,
    layer_const_mul, layer_const_mul, hy, hx, hy2, hx2]
  ring

/-- Exact maximal bad-event price for the theta=1/2 stage-350 envelope.
The estimate is valid for every real x and all y<=4/9. -/
theorem half_quadratic_bad_bound {y x theta : ℝ} (hy : y ≤ 4 / 9) (ht : |theta| ≤ 1 / 2) :
    quadratic (99 / 100) (3 / 5) 2 theta y x ≤ 24451 / 32400 := by
  have htheta : theta ^ 2 ≤ 1 / 4 := by
    have h1 := (abs_le.mp ht).1
    have h2 := (abs_le.mp ht).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ theta + 1 / 2) (by linarith : 0 ≤ 1 / 2 - theta)]
  have hx : -theta * x - (3 / 5) * x ^ 2 ≤ 5 / 48 := by
    nlinarith [sq_nonneg ((6 / 5) * x + theta)]
  have hy' : -(y - 1) / 2 - 2 * (y - 1) ^ 2 ≤ 5 / 18 - 50 / 81 := by
    have hp : 0 ≤ (4 / 9 - y) * (2 * (2 - 4 / 9 - y) - 1 / 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  unfold quadratic
  linarith

theorem quadratic_expectation_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k nu H a B theta R D : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m) :
    H - a * R - B * D / m ≤ hardCoreLayerExpectation G S I z (fun j M =>
      quadratic H a B theta ((M : ℝ) / m)
        ((k - binomialLayerMean j M z) / Real.sqrt (nu * m))) := by
  rw [quadratic_expectation G S I hIS hI hz hm hm0 hmean hnu]
  have hL : (hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m) / (nu * m) ≤ R :=
    (div_le_iff₀ (mul_pos hnu hm0)).mpr hvarL
  have hM : hardCoreAvailableVariance G S I z / m ^ 2 ≤ D / m := by
    calc
      _ ≤ (D * m) / m ^ 2 := div_le_div_of_nonneg_right hvarM (sq_nonneg m)
      _ = _ := by field_simp
  have hL' := mul_le_mul_of_nonneg_left hL ha
  have hM' := mul_le_mul_of_nonneg_left hM hB
  rw [mul_div_assoc]
  linarith

#print axioms quadratic_expectation
#print axioms half_quadratic_bad_bound
#print axioms quadratic_expectation_lower
end ForestUnimodality.GaussianDirectionalLayerBudget
