import ForestUnimodality.HardCoreBipartiteVariance
import ForestUnimodality.ForestIndependenceBound
import Mathlib.Analysis.Real.Sqrt

/-! Actual growth of the hard-core mean on bipartite graphs. The adjusted-mean
inequality used for the final activity window remains an explicit input; this
module proves the intervening differential and numerical implications. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem hardCoreMean_nonneg (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hardCoreMean G S z := by
  unfold hardCoreMean hardCoreMomentNumerator
  exact div_nonneg (sum_nonneg fun J _ => mul_nonneg (by positivity) (pow_nonneg hz _))
    (partitionFunction_pos G S hz).le

noncomputable def hardCoreMeanGrowthQuantity (G : SimpleGraph V) (S : Finset V)
    (z : ℝ) : ℝ := hardCoreMean G S z ^ 2 * (1 + z) / z

theorem hasDerivAt_hardCoreMeanGrowthQuantity (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (hardCoreMeanGrowthQuantity G S)
      (hardCoreMean G S z *
        (2 * (1 + z) * hardCoreVariance G S z - hardCoreMean G S z) / z ^ 2) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hd := (((hasDerivAt_hardCoreMean G S hz).pow 2).mul
    ((hasDerivAt_id z).const_add 1)).div (hasDerivAt_id z) hzne
  apply hd.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one]
  field_simp
  ring

/-- The monotone quantity is defined even for empty graphs and avoids
division by the mean or logarithms of it. -/
theorem hardCoreMeanGrowthQuantity_monotoneOn_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V) :
    MonotoneOn (hardCoreMeanGrowthQuantity G S) (Set.Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro z hz
    exact (hasDerivAt_hardCoreMeanGrowthQuantity G S hz).continuousAt.continuousWithinAt
  · intro z hz
    have hzpos : 0 < z := by simpa only [interior_Ioi, Set.mem_Ioi] using hz
    exact (hasDerivAt_hardCoreMeanGrowthQuantity G S hzpos).differentiableAt.differentiableWithinAt
  · intro z hz
    have hzpos : 0 < z := by simpa only [interior_Ioi, Set.mem_Ioi] using hz
    rw [(hasDerivAt_hardCoreMeanGrowthQuantity G S hzpos).deriv]
    have hv := hardCoreVariance_ge_half_mean_div_one_add_of_isBipartite G hG S hzpos
    have hv' : hardCoreMean G S z ≤ 2 * (1 + z) * hardCoreVariance G S z := by
      have hden : 0 < 2 * (1 + z) := by positivity
      have h := (div_le_iff₀ hden).mp hv
      nlinarith
    exact div_nonneg (mul_nonneg (hardCoreMean_nonneg G S hzpos.le)
      (sub_nonneg.mpr hv')) (sq_nonneg _)

/-- Denominator-cleared mean growth between any two positive activities. -/
theorem hardCoreMean_sq_growth_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b * (1 + a) * hardCoreMean G S a ^ 2 ≤
      a * (1 + b) * hardCoreMean G S b ^ 2 := by
  have hb := ha.trans_le hab
  have h := hardCoreMeanGrowthQuantity_monotoneOn_of_isBipartite G hG S ha hb hab
  unfold hardCoreMeanGrowthQuantity at h
  have h' := (div_le_div_iff₀ ha hb).mp h
  nlinarith

/-- The exact activity growth factor used at the upper end of the window. -/
theorem hardCoreMean_two_mul_sqrt_le_nine_quarters_of_isBipartite
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V) :
    Real.sqrt (27 / 26 : ℝ) * hardCoreMean G S 2 ≤ hardCoreMean G S (9 / 4) := by
  have hg := hardCoreMean_sq_growth_of_isBipartite G hG S
    (a := 2) (b := 9 / 4) (by norm_num) (by norm_num)
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27 / 26)
  have hsq : (Real.sqrt (27 / 26 : ℝ) * hardCoreMean G S 2) ^ 2 ≤
      hardCoreMean G S (9 / 4) ^ 2 := by
    rw [mul_pow, hsqrt]
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (hardCoreMean_nonneg G S (by norm_num)))
    (hardCoreMean_nonneg G S (by norm_num))).mp hsq

theorem hardCoreMean_two_mul_sqrt_le_nine_quarters_of_isAcyclic
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    Real.sqrt (27 / 26 : ℝ) * hardCoreMean G S 2 ≤ hardCoreMean G S (9 / 4) :=
  hardCoreMean_two_mul_sqrt_le_nine_quarters_of_isBipartite G hG.isBipartite S

theorem sixty_div_fiftyNine_lt_sqrt_growth : (60 / 59 : ℝ) < Real.sqrt (27 / 26 : ℝ) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27 / 26)
  have hn := Real.sqrt_nonneg (27 / 26 : ℝ)
  nlinarith

/-- The structural M inequality is explicit. Everything after it, including
the strict numerical margin at a=n/2, is proved here. -/
theorem hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean
    (G : SimpleGraph V) (hG : G.IsBipartite) (S : Finset V) (hS : S.Nonempty)
    (a : ℕ) (hhalf : S.card ≤ 2 * a)
    (hM : (a : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2) :
    ((S.card : ℝ) + 2 * (a : ℝ)) / 6 < hardCoreMean G S (9 / 4) := by
  have hhalfR : (S.card : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hhalf
  have hlinear : ((S.card : ℝ) + 2 * (a : ℝ)) / 6 ≤
      (60 / 59 : ℝ) * hardCoreMean G S 2 := by linarith
  have hpos := hardCoreMean_pos G S hS (z := 2) (by norm_num)
  have hstrict := mul_lt_mul_of_pos_right sixty_div_fiftyNine_lt_sqrt_growth hpos
  exact (hlinear.trans_lt hstrict).trans_le
    (hardCoreMean_two_mul_sqrt_le_nine_quarters_of_isBipartite G hG S)

/-- A forest's actual maximum independent cardinality supplies the half-order
condition. M remains the one explicit structural assumption. -/
theorem IsMaximumIndependentOn.hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (hS : S.Nonempty)
    (hM : (I.card : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2) :
    ((S.card : ℝ) + 2 * (I.card : ℝ)) / 6 < hardCoreMean G S (9 / 4) :=
  ForestUnimodality.hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean G hG.isBipartite S hS I.card
    (hI.card_le_two_mul_of_isAcyclic hG) hM

/-- The true lower endpoint, the proved growth step, and explicit M give a
unique activity throughout the requested rank interval. -/
theorem IsMaximumIndependentOn.existsUnique_activity_window_of_adjusted_mean
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (hS : S.Nonempty)
    (hM : (I.card : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2)
    (k : ℝ) (hklo : (S.card : ℝ) / 4 ≤ k)
    (hkhi : k ≤ ((S.card : ℝ) + 2 * (I.card : ℝ)) / 6) :
    ∃! z : ℝ, z ∈ Set.Icc (1 / 3) (9 / 4) ∧ hardCoreMean G S z = k := by
  apply existsUnique_activity_of_mean_bracket G S hS (by norm_num) (by norm_num)
  · exact (hardCoreMean_one_third_le G S).trans hklo
  · exact hkhi.trans (hI.hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean hG hS hM).le

#print axioms hardCoreMeanGrowthQuantity_monotoneOn_of_isBipartite
#print axioms hardCoreMean_two_mul_sqrt_le_nine_quarters_of_isAcyclic
#print axioms IsMaximumIndependentOn.hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean
#print axioms IsMaximumIndependentOn.existsUnique_activity_window_of_adjusted_mean

end ForestUnimodality
