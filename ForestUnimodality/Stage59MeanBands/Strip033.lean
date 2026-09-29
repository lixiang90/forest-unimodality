import ForestUnimodality.Stage59KernelData.Cell037.Conclusion
import ForestUnimodality.Stage59KernelData.Cell038.Conclusion

/-! Actual forest mean cover on one activity strip. The upper mean bound
is retained; global activity coverage requires the higher-stage handoff. -/
namespace ForestUnimodality.Stage59MeanBands.Strip033
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def meanLower : ℚ := Stage59KernelData.Cell037.mlo
def meanUpper : ℚ := Stage59KernelData.Cell038.mhi

theorem available_mean_lower {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59≤S.card) (hN : S.card≤79) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1687/3572:ℝ) (9/19:ℝ))
    (hmean : hardCoreMean G S z=k) :
    (meanLower:ℝ)≤hardCoreAvailableMean G S B z := by
  have hqf : z/(1+z)∈Set.Icc (Stage59KernelData.Cell037.interval.lo:ℝ) (Stage59KernelData.Cell037.interval.hi:ℝ) := by
    simpa [Stage59KernelData.Cell037.interval] using hq
  have hd := Stage59KernelData.Cell037.actual_density G hG S hn hN (Stage59KernelData.Cell037.activity_bounds hz hqf).1
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hnR (by norm_num [Stage59KernelData.Cell037.density] : (0:ℝ)≤Stage59KernelData.Cell037.density)
  have hk : 16≤k := FiniteMarginalSupport.integer_rank_lower
    (by nlinarith [hd] : (59*(Stage59KernelData.Cell037.density:ℝ))≤(k:ℝ)) (by norm_num [Stage59KernelData.Cell037.density])
  have hkR : (16:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have hh := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,
    hmean] at hh
  have hmul := mul_le_mul_of_nonneg_right hq.2 (hardCoreAvailableMean_nonneg G S B hz.le)
  norm_num [meanLower,Stage59KernelData.Cell037.mlo]
  linarith

theorem no_weak_valley_of_mean_upper {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59≤S.card) (hN : S.card≤79) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1687/3572:ℝ) (9/19:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hupper : hardCoreAvailableMean G S B z≤(meanUpper:ℝ)) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hlo := available_mean_lower k hB hG hn hN hz hq hmean
  by_cases h0 : hardCoreAvailableMean G S B z≤(Stage59KernelData.Cell037.mhi:ℝ)
  · apply Stage59KernelData.Cell037.actual_no_weak_valley k hB hG hn hN hz
      (by simpa [Stage59KernelData.Cell037.interval] using hq) hrank hmean
    exact ⟨(by simpa only [meanLower] using hlo),h0⟩
  apply Stage59KernelData.Cell038.actual_no_weak_valley k hB hG hn hN hz
    (by simpa [Stage59KernelData.Cell038.interval] using hq) hrank hmean
  exact ⟨(by simpa only [Stage59KernelData.Cell037.mhi,Stage59KernelData.Cell038.mlo] using (le_of_not_ge h0)),(by simpa only [meanUpper] using hupper)⟩

theorem mean_above_of_weak_valley {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59≤S.card) (hN : S.card≤79) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1687/3572:ℝ) (9/19:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hvalley : countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) :
    (meanUpper:ℝ)<hardCoreAvailableMean G S B z := by
  by_contra h
  exact no_weak_valley_of_mean_upper k hB hG hn hN hz hq hrank hmean (le_of_not_gt h) hvalley

#print axioms available_mean_lower
#print axioms no_weak_valley_of_mean_upper
#print axioms mean_above_of_weak_valley
end ForestUnimodality.Stage59MeanBands.Strip033
