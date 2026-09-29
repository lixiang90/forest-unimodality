import ForestUnimodality.Stage59ExactVarianceData.Batch202_230
import ForestUnimodality.Stage59KernelData.Cell212.Density
import ForestUnimodality.Stage59KernelData.Cell212.Budget
import ForestUnimodality.Stage59KernelData.Cell212.Counts
import ForestUnimodality.Stage170SourceData.Windows.Batch060_079

namespace ForestUnimodality.Stage59KernelData.Cell212
open FiniteMarginalSupport
variable {V : Type*} [DecidableEq V]

theorem probability_bounds {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    q ∈ Set.Icc ((27 / 47) : ℝ) ((653 / 1128) : ℝ) := by
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
    (hhalf : 2*k≤S.card)
    (hm : hardCoreAvailableMean G S B z ≤ (mhi : ℝ)) :
    (S.card, k) ∈ pairs := by
  have hnR : (59 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hdensity := actual_density G hG S hn hN (activity_bounds hz hq).1
  have hρn := mul_le_mul_of_nonneg_left hnR (by norm_num [density] : (0:ℝ)≤density)
  have hklo : 18 ≤ k := integer_rank_lower
    (by nlinarith : (59*(density:ℝ))≤(k:ℝ)) (by norm_num [density])
  have hgeom : (parameters.density:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
    simpa only [parameters,density] using hdensity
  have hqhi : z / (1 + z) ≤ ((653 / 1128) : ℝ) := (probability_bounds hq).2
  have hmass := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz] at hmass
  have hm0 := hardCoreAvailableMean_nonneg G S B hz.le
  have hmul := mul_le_mul hqhi hm hm0 (by norm_num : (0 : ℝ) ≤ (653 / 1128))
  have hkupper : (k : ℝ) ≤ 2 * ((653 / 1128) : ℝ) * (mhi : ℝ) := by linarith
  have hkhi : k ≤ 29 := integer_rank_upper hkupper (by norm_num [mhi])
  rw [← pairs_checked]
  apply parameters.actual_mem_pairs G S hz k hmean hn hN hklo hkhi hrank hhalf
  · exact hgeom
  · simpa [parameters] using hqhi

theorem actual_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + (alpha : ℝ)) *
        hardCoreAvailableMean G S B z + 0 := by
  simpa only [alpha, Stage59ExactVarianceData.Cell212.alpha] using
    Stage59ExactVarianceData.Cell212.actual_variance hB hG hz (probability_bounds hq)

theorem actual_available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hS : 0 < S.card)
    (hq : z / (1 + z) ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z ≤ (D : ℝ) * hardCoreAvailableMean G S B z := by
  have hqw : z / (1+z) ∈ Set.Icc (Stage170SourceData.Window060.window.qa : ℝ) (Stage170SourceData.Window060.window.qb : ℝ) := by
    norm_num [Stage170SourceData.Window060.window]
    exact probability_bounds hq
  exact Stage170SourceData.Window060.window.available_variance Stage170SourceData.Window060.valid hB hG hz hS hqw hrank

#print axioms actual_pair
#print axioms actual_variance
#print axioms actual_available_variance
end ForestUnimodality.Stage59KernelData.Cell212
