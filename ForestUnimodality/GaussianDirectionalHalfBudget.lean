import ForestUnimodality.GaussianDirectionalHalf
import ForestUnimodality.GaussianDirectionalLayerBudget

/-! A proved real Gaussian directional budget under the actual hard-core
layer law. The source variance and tail inputs remain explicit, while the
pointwise Gaussian envelope and both zero-mean identities are discharged. -/
namespace ForestUnimodality.GaussianDirectionalHalfBudget

open GaussianDirectionalEnvelope GaussianDirectionalLayerBudget NegativePowerLayerBudget

variable {V : Type*} [DecidableEq V]

theorem actual_layer_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k nu theta R D epsilon : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (ht : |theta| ≤ 1 / 2)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (htail : hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ epsilon) :
    99 / 100 - (3 / 5) * R - 2 * D / m - (24451 / 32400) * epsilon ≤
      hardCoreLayerExpectation G S I z (fun j M =>
        if (4 / 9) * m ≤ (M : ℝ) then
          kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta
        else 0) := by
  have hpoint (j M : ℕ) :
      quadratic (99 / 100) (3 / 5) 2 theta ((M : ℝ) / m)
          ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) -
        (24451 / 32400) * (if (M : ℝ) < (4 / 9) * m then 1 else 0) ≤
      if (4 / 9) * m ≤ (M : ℝ) then
        kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0 := by
    by_cases hg : (4 / 9) * m ≤ (M : ℝ)
    · simp only [if_pos hg, if_neg (not_lt.mpr hg), mul_zero, sub_zero]
      exact GaussianDirectionalHalf.envelope ((le_div_iff₀ hm0).mpr hg) ht _
    · simp only [if_neg hg, if_pos (lt_of_not_ge hg), mul_one]
      have hy : (M : ℝ) / m ≤ 4 / 9 := (div_le_iff₀ hm0).mpr (le_of_not_ge hg)
      exact sub_nonpos.mpr (half_quadratic_bad_bound hy ht)
  have hraw := layer_mono G S I hz.le _ _ hpoint
  rw [layer_sub, layer_const_mul] at hraw
  change hardCoreLayerExpectation G S I z (fun j M =>
      quadratic (99 / 100) (3 / 5) 2 theta ((M : ℝ) / m)
        ((k - binomialLayerMean j M z) / Real.sqrt (nu * m))) -
      (24451 / 32400) * hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ _ at hraw
  have hquad := quadratic_expectation_lower G S I hIS hI hz hm hm0 hmean hnu
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (0 : ℝ) ≤ 2) hvarL hvarM
    (H := 99 / 100) (theta := theta)
  have hcost := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 24451 / 32400)
  linarith

#print axioms actual_layer_lower
end ForestUnimodality.GaussianDirectionalHalfBudget
