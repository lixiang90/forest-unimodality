import ForestUnimodality.BinomialGradientThirtyOneLarge
import ForestUnimodality.FiniteGradientCoverage

/-! The all-degree .31 gradient on the entire reflected parameter interval. -/
namespace ForestUnimodality.BinomialGradientThirtyOne
open Real

theorem gradient_bound (d : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 3 / 10 ≤ q) (hq1 : q ≤ 7 / 10) :
    |binomialMass d j q - binomialMass d (j - 1) q| ≤
      (31 / 100) / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  by_cases hd : 20 ≤ d
  · exact large_gradient_bound d hd j hq0 hq1
  · have hq : q ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hv : 0 < q * (1 - q) := mul_pos hq.1 (sub_pos.mpr hq.2)
    have hD : 0 < ((d + 1 : ℕ) : ℝ) * (q * (1 - q)) := by positivity
    have he := FiniteGradientCoverage.bound (d + 1) j (by omega) (by omega) ⟨hq0,hq1⟩
    rw [binomial_gradient_identity d j hv.ne', abs_mul, abs_div, abs_of_pos hD,
      abs_of_nonneg (binomialMass_nonneg (d+1) j hq.1.le hq.2.le), div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right he hD.le

theorem gradient_bound_succ (d : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 3 / 10 ≤ q) (hq1 : q ≤ 7 / 10) :
    |binomialMass d (j + 1) q - binomialMass d j q| ≤
      (31 / 100) / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  simpa using gradient_bound d (j+1) hq0 hq1

#print axioms gradient_bound
#print axioms gradient_bound_succ
end ForestUnimodality.BinomialGradientThirtyOne
