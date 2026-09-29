import ForestUnimodality.Stage170Windows.Strip027.Complete
import ForestUnimodality.Stage130KernelData.Cell027.Conclusion
import ForestUnimodality.Stage99KernelData.Cell027.Conclusion
import ForestUnimodality.Stage80KernelData.Cell027.Conclusion
import ForestUnimodality.Stage59KernelData.Cell027.Conclusion
import ForestUnimodality.Stage59MeanBands.Strip027

/-! Complete mean coverage on one activity interval, for orders 59 through 349.
This is a restricted-activity theorem, not all-order unimodality. -/
namespace ForestUnimodality.BridgeActivityData.Strip027
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_valley_of_parent_mean {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤349)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : ((strip 27).mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hqs : z/(1+z)∈Set.Icc ((strip 27).qlo:ℝ) ((strip 27).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc ((301/666:ℚ):ℝ) ((17/37:ℚ):ℝ)
    norm_num
    exact hq
  by_cases hhi : hardCoreAvailableMean G S B z≤((strip 27).mhi:ℝ)
  · obtain ⟨i,hi,hpoint⟩ := (strip 27).check_sound rectangle strip027_checked hqs ⟨hm,hhi⟩
    change i∈([455,376,109,110,111,112,113] : List (Fin 558)) at hi
    have hc : i=455 ∨ i=376 ∨ i=109 ∨ i=110 ∨ i=111 ∨ i=112 ∨ i=113 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell455.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell376.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell109.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell110.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell111.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell112.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell113.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · have hp := (strip 27).parent_domain (window 27) 170
      Stage170SourceData.Window027.valid source027_checked hz hqs (le_of_not_ge hhi)
    exact Stage350ParentHandoff.no_weak_valley (window 27).parent
      k hB hG hS hp.2 hp.1 hrank hmean hk

#print axioms no_valley_of_parent_mean

theorem no_valley_of_mean_130 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤169)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage130KernelData.Cell027.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hS : 0<S.card := by omega
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage130KernelData.Cell027.mhi:ℝ)
  · exact Stage130KernelData.Cell027.actual_no_weak_valley k hB hG hS hN hz hk
      (by simpa [Stage130KernelData.Cell027.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage130KernelData.Cell027.mhi:ℝ)=((strip 27).mlo:ℝ) := rfl
    apply no_valley_of_parent_mean k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_130

theorem no_valley_of_mean_99 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤129)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage99KernelData.Cell027.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hS : 0<S.card := by omega
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage99KernelData.Cell027.mhi:ℝ)
  · exact Stage99KernelData.Cell027.actual_no_weak_valley k hB hG hS hN hz hk
      (by simpa [Stage99KernelData.Cell027.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage99KernelData.Cell027.mhi:ℝ)=(Stage130KernelData.Cell027.mlo:ℝ) := rfl
    apply no_valley_of_mean_130 k hB hG hn (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_99

theorem no_valley_of_mean_80 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤98)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage80KernelData.Cell027.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hS : 0<S.card := by omega
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage80KernelData.Cell027.mhi:ℝ)
  · exact Stage80KernelData.Cell027.actual_no_weak_valley k hB hG hS (by omega) hN hz hk
      (by simpa [Stage80KernelData.Cell027.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage80KernelData.Cell027.mhi:ℝ)=(Stage99KernelData.Cell027.mlo:ℝ) := rfl
    apply no_valley_of_mean_99 k hB hG hn (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_80

theorem no_valley_of_mean_59 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤79)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (_hm : (Stage59KernelData.Cell027.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage59MeanBands.Strip027.meanUpper:ℝ)
  · exact Stage59MeanBands.Strip027.no_weak_valley_of_mean_upper k hB hG hn hN hz hq hrank hmean hhi
  · have he : (Stage59MeanBands.Strip027.meanUpper:ℝ)=(Stage99KernelData.Cell027.mlo:ℝ) := rfl
    apply no_valley_of_mean_99 k hB hG hn (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_59

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (301/666:ℝ) (17/37:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hn170 : 170≤S.card
  · exact Stage170Windows.Strip027.no_weak_valley k hG hn170 hN hz hq hrank hmean
  obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  change IsMaximumMarginalIndependentOn G S B z at hB
  have hS : 0<S.card := by omega
  have hkr : (S.card:ℝ)/4≤(k:ℝ) := by simpa only [hmean] using hrank
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  have hh := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,
    hmean] at hh
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hmul := mul_le_mul_of_nonneg_right hq.2 hm
  have hav : (k:ℝ)≤2*(17/37:ℝ)*hardCoreAvailableMean G S B z := by nlinarith
  by_cases hn130 : 130≤S.card
  · have hstage : (130:ℝ)≤S.card := by exact_mod_cast hn130
    have hnat : 33≤k := by
      by_contra h
      have hku : (k:ℝ)≤32 := by exact_mod_cast (show k≤32 by omega)
      linarith
    have hkl : (33:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_130 k hB hG hn (by omega) hz hk hq hrank hmean
    norm_num [Stage130KernelData.Cell027.mlo]
    linarith
  by_cases hn99 : 99≤S.card
  · have hstage : (99:ℝ)≤S.card := by exact_mod_cast hn99
    have hnat : 25≤k := by
      by_contra h
      have hku : (k:ℝ)≤24 := by exact_mod_cast (show k≤24 by omega)
      linarith
    have hkl : (25:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_99 k hB hG hn (by omega) hz hk hq hrank hmean
    norm_num [Stage99KernelData.Cell027.mlo]
    linarith
  by_cases hn80 : 80≤S.card
  · have hstage : (80:ℝ)≤S.card := by exact_mod_cast hn80
    have hdensity := Stage80SourceData.Cell027.actual_density G hG S (by omega) (by omega) hz
      (by simpa [Stage80KernelData.Cell027.interval] using hq) hrank
    rw [hmean] at hdensity
    have hdensityLower := mul_le_mul_of_nonneg_left hstage
      (by norm_num [Stage80SourceData.Cell027.density] : (0:ℝ)≤Stage80SourceData.Cell027.density)
    have hdensityRank : (20:ℝ)<(Stage80SourceData.Cell027.density:ℝ)*80 := by
      norm_num [Stage80SourceData.Cell027.density]
    have hnat : 21≤k := by
      by_contra h
      have hku : (k:ℝ)≤20 := by exact_mod_cast (show k≤20 by omega)
      linarith [hdensity,hdensityLower,hdensityRank]
    have hkl : (21:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_80 k hB hG hn (by omega) hz hk hq hrank hmean
    norm_num [Stage80KernelData.Cell027.mlo]
    linarith
  have hstage : (59:ℝ)≤S.card := hnR
  have hdensity := Stage59KernelData.Cell027.actual_density G hG S hn (by omega)
    (Stage59KernelData.Cell027.activity_bounds hz (by simpa [Stage59KernelData.Cell027.interval] using hq)).1
  rw [hmean] at hdensity
  have hdensityLower := mul_le_mul_of_nonneg_left hstage
    (by norm_num [Stage59KernelData.Cell027.density] : (0:ℝ)≤Stage59KernelData.Cell027.density)
  have hdensityRank : (15:ℝ)<(Stage59KernelData.Cell027.density:ℝ)*59 := by
    norm_num [Stage59KernelData.Cell027.density]
  have hnat : 16≤k := by
    by_contra h
    have hku : (k:ℝ)≤15 := by exact_mod_cast (show k≤15 by omega)
    linarith [hdensity,hdensityLower,hdensityRank]
  have hkl : (16:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
  apply no_valley_of_mean_59 k hB hG hn (by omega) hz hk hq hrank hmean
  norm_num [Stage59KernelData.Cell027.mlo]
  linarith

#print axioms no_weak_valley
end ForestUnimodality.BridgeActivityData.Strip027
