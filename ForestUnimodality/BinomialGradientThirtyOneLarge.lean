import ForestUnimodality.BinomialGradientConstants

/-! A smaller exact entropy threshold for the fixed .31 constant. -/
namespace ForestUnimodality.BinomialGradientThirtyOne
open BinomialGradientConstants BinomialGradientEnvelope

theorem thirtyOne_valid : Valid (21 / 10) (2 / 5) (3 / 10) (31 / 100) := by
  constructor <;> norm_num [X, R, K, piLower, eLower]

theorem large_gradient_bound (d : ℕ) (hd : 20 ≤ d) (j : ℤ) {q : ℝ}
    (hq0 : 3 / 10 ≤ q) (hq1 : q ≤ 7 / 10) :
    |binomialMass d j q - binomialMass d (j - 1) q| ≤
      (31 / 100) / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  have hv : 21 / 100 ≤ q * (1 - q) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr hq1)]
  have hD : (21 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 21 ≤ d + 1 by omega)
  apply gradient_bound d j thirtyOne_valid hq0 (by linarith) ?_ ?_
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have he := mul_le_mul hD hv (by norm_num) (by positivity : (0:ℝ) ≤ ((d+1:ℕ):ℝ))
    nlinarith

#print axioms thirtyOne_valid
#print axioms large_gradient_bound
end ForestUnimodality.BinomialGradientThirtyOne
