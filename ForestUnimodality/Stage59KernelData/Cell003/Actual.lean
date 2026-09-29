import ForestUnimodality.Stage59KernelData.Cell003.Budget
import ForestUnimodality.Stage59KernelData.Cell003.Counts
import ForestUnimodality.Stage170SourceData.Windows.Batch000_019

namespace ForestUnimodality.Stage59KernelData.Cell003
open FiniteMarginalSupport
variable {V : Type*} [DecidableEq V]

theorem probability_bounds {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    q ∈ Set.Icc ((19 / 70) : ℝ) ((39 / 140) : ℝ) := by
  norm_num [interval] at hq ⊢
  exact hq

theorem activity_bounds {z : ℝ} (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    (activityLower : ℝ) ≤ z ∧ z ≤ (activityUpper : ℝ) := by
  have hlo := (le_div_iff₀ (by positivity : 0 < 1 + z)).mp hq.1
  have hhi := (div_le_iff₀ (by positivity : 0 < 1 + z)).mp hq.2
  norm_num [interval, activityLower, activityUpper] at *
  constructor <;> linarith

theorem actual_pair {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ≤ (mhi : ℝ)) :
    (S.card, k) ∈ pairs := by
  have hnR : (59 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hklo : 15 ≤ k := integer_rank_lower (by linarith : (59 / 4 : ℝ) ≤ (k : ℝ)) (by norm_num)
  have hqhi : z / (1 + z) ≤ ((39 / 140) : ℝ) := (probability_bounds hq).2
  have hmeanUpper := hardCoreMean_le_card_mul_activity G S hz.le
  rw [hmean, mul_div_assoc] at hmeanUpper
  have hmq := mul_le_mul_of_nonneg_left hqhi (Nat.cast_nonneg S.card : (0 : ℝ) ≤ _)
  have hhalfR : 2 * (k : ℝ) ≤ S.card := by
    nlinarith [show (0 : ℝ) ≤ S.card from Nat.cast_nonneg _]
  have hhalf : 2 * k ≤ S.card := by exact_mod_cast hhalfR
  have hmass := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hmass
  have hm0 := hardCoreAvailableMean_nonneg G S B hz.le
  have hmul := mul_le_mul hqhi hm hm0 (by norm_num : (0 : ℝ) ≤ (39 / 140))
  have hkupper : (k : ℝ) ≤ 2 * ((39 / 140) : ℝ) * (mhi : ℝ) := by linarith
  have hkhi : k ≤ 24 := integer_rank_upper hkupper (by norm_num [mhi])
  rw [← pairs_checked]
  apply parameters.actual_mem_pairs G S hz k hmean hn hN hklo hkhi hrank hhalf
  · norm_num [parameters]
    linarith
  · simpa [parameters] using hqhi

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + (alpha : ℝ)) *
        hardCoreAvailableMean G S B z + 0 := by
  have hqw : z / (1+z) ∈ Set.Icc (Stage170SourceData.Window003.window.qa : ℝ) (Stage170SourceData.Window003.window.qb : ℝ) := by
    norm_num [Stage170SourceData.Window003.window]
    exact probability_bounds hq
  convert Stage170SourceData.Window003.window.total_variance Stage170SourceData.Window003.valid hB hG hz hqw using 1
  norm_num [alpha, Stage170SourceData.Window003.window]

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hS : 0 < S.card)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z ≤ (D : ℝ) * hardCoreAvailableMean G S B z := by
  have hqw : z / (1+z) ∈ Set.Icc (Stage170SourceData.Window003.window.qa : ℝ) (Stage170SourceData.Window003.window.qb : ℝ) := by
    norm_num [Stage170SourceData.Window003.window]
    exact probability_bounds hq
  exact Stage170SourceData.Window003.window.available_variance Stage170SourceData.Window003.valid hB hG hz hS hqw hrank

#print axioms actual_pair
#print axioms actual_variance
#print axioms actual_available_variance
end ForestUnimodality.Stage59KernelData.Cell003
