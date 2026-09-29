import ForestUnimodality.ActivityDensityTransfer
import ForestUnimodality.HardCoreActivityGrowth

/-! The exact two density regimes used in central-rank budgets.  The lower
activity regime retains the necessary rank bound; the upper regime uses
the proved bipartite variance growth, never path extremality at other activities. -/
namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem forest_density_of_upper_activity_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {a z ρ : ℝ} (ha : 1 ≤ a) (haz : a ≤ z) (hρ : 0 ≤ ρ)
    (hcert : (1 + a) * ρ ^ 2 ≤ 2 * a * (276393 / 1000000 : ℝ) ^ 2) :
    ρ * (S.card : ℝ) ≤ hardCoreMean G S z := by
  have ha0 : 0 < a := by linarith
  have h0 := UnitActivityForestDensity.mean_density_lower G hG S
  have h0sq : ((276393 / 1000000 : ℝ) * (S.card : ℝ)) ^ 2 ≤ hardCoreMean G S 1 ^ 2 :=
    (sq_le_sq₀ (by positivity) (hardCoreMean_nonneg G S (by norm_num))).mpr h0
  have hg := hardCoreMean_sq_growth_of_isBipartite G hG.isBipartite S
    (a := 1) (b := a) (by norm_num) ha
  norm_num only [one_add_one_eq_two, one_mul] at hg
  have hn := mul_le_mul_of_nonneg_right hcert (sq_nonneg (S.card : ℝ))
  have hm := mul_le_mul_of_nonneg_left h0sq (show 0 ≤ 2 * a by positivity)
  have hsq : (ρ * (S.card : ℝ)) ^ 2 ≤ hardCoreMean G S a ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1 + a by positivity)).mp
    nlinarith
  have hpa : ρ * (S.card : ℝ) ≤ hardCoreMean G S a :=
    (sq_le_sq₀ (mul_nonneg hρ (Nat.cast_nonneg _)) (hardCoreMean_nonneg G S ha0.le)).mp hsq
  by_cases hS : S.Nonempty
  · exact hpa.trans ((hardCoreMean_strictMonoOn G S hS).monotoneOn ha0 (ha0.trans_le haz) haz)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [hardCoreMean, hardCoreMomentNumerator, independentSubsets_empty_eq_singleton]

theorem log_lower_rational (a : ℝ) (ha : 0 < a) : -(1 - a) / a ≤ Real.log a := by
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
  rw [Real.log_inv] at hh
  have he : -(1 - a) / a = 1 - a⁻¹ := by field_simp; ring
  rw [he]
  linarith

theorem forest_density_of_lower_activity_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {a z A ρ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haz : a ≤ z) (hA : 43 / 100 ≤ A)
    (hcert : ρ ≤ 276393 / 1000000 - A * (1 - a) / a) :
    ρ * (S.card : ℝ) ≤ hardCoreMean G S z := by
  apply forest_mean_density_lower_of_log_enclosure G hG S (ha.trans_le haz)
    (L := -(1 - a) / a)
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  · exact (log_lower_rational a ha).trans (Real.log_le_log ha haz)
  · have hh := mul_nonneg (sub_nonneg.mpr hA)
      (div_nonneg (sub_nonneg.mpr ha1) ha.le)
    have he : A * (1 - a) / a = A * ((1 - a) / a) := by ring
    rw [he] at hcert
    rw [neg_div]
    nlinarith

theorem forest_central_density_of_lower_activity_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {a z A ρ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haz : a ≤ z) (hA : 43 / 100 ≤ A)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hcert : ρ ≤ max (1 / 4) (276393 / 1000000 - A * (1 - a) / a)) :
    ρ * (S.card : ℝ) ≤ hardCoreMean G S z := by
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  by_cases hh : 276393 / 1000000 - A * (1 - a) / a ≤ 1 / 4
  · rw [max_eq_left hh] at hcert
    nlinarith [mul_le_mul_of_nonneg_right hcert hn]
  · rw [max_eq_right (le_of_not_ge hh)] at hcert
    exact forest_density_of_lower_activity_certificate G hG S ha ha1 haz hA hcert

#print axioms forest_density_of_upper_activity_certificate
#print axioms forest_density_of_lower_activity_certificate
#print axioms forest_central_density_of_lower_activity_certificate
end ForestUnimodality
