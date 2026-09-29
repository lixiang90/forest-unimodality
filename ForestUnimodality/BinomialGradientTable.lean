import ForestUnimodality.BinomialGradientConstants

/-! Eight fixed stage-900 gradient constants, checked with exact rational
arithmetic and then applied to the actual binomial law. -/
namespace ForestUnimodality.BinomialGradientTable
open BinomialGradientConstants BinomialGradientEnvelope

noncomputable def scale : Fin 4 → ℝ := ![3, 5, 7, 10]
noncomputable def generalConstant : Fin 4 → ℝ := ![279 / 1000, 261 / 1000, 255 / 1000, 251 / 1000]
noncomputable def nearConstant : Fin 4 → ℝ := ![255 / 1000, 248 / 1000, 246 / 1000, 245 / 1000]

theorem general_valid (i : Fin 4) : Valid (scale i) (2 / 5) (3 / 10) (generalConstant i) := by
  fin_cases i <;> constructor <;>
    norm_num [scale, generalConstant, X, R, K, piLower, eLower]

theorem near_valid (i : Fin 4) : Valid (scale i) (1 / 10) (9 / 20) (nearConstant i) := by
  fin_cases i <;> constructor <;>
    norm_num [scale, nearConstant, X, R, K, piLower, eLower]

theorem general_gradient_bound (i : Fin 4) (d : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 3 / 10 ≤ q) (hq1 : q ≤ 7 / 10)
    (hvar : (scale i) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) * (q * (1 - q))) :
    |binomialMass d j q - binomialMass d (j - 1) q| ≤
      generalConstant i / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  apply gradient_bound d j (general_valid i) hq0 (by linarith) ?_ hvar
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem near_gradient_bound (i : Fin 4) (d : ℕ) (j : ℤ) {q : ℝ}
    (hq0 : 9 / 20 ≤ q) (hq1 : q ≤ 11 / 20)
    (hvar : (scale i) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) * (q * (1 - q))) :
    |binomialMass d j q - binomialMass d (j - 1) q| ≤
      nearConstant i / (((d + 1 : ℕ) : ℝ) * (q * (1 - q))) := by
  apply gradient_bound d j (near_valid i) hq0 (by linarith) ?_ hvar
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms general_valid
#print axioms near_valid
#print axioms general_gradient_bound
#print axioms near_gradient_bound
end ForestUnimodality.BinomialGradientTable
