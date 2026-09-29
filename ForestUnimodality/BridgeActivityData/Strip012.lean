import ForestUnimodality.Stage170Windows.Strip012.Complete
import ForestUnimodality.Stage130KernelData.Cell012.Conclusion
import ForestUnimodality.Stage99KernelData.Cell012.Conclusion
import ForestUnimodality.Stage80KernelData.Cell012.Conclusion
import ForestUnimodality.Stage59KernelData.Cell012.Conclusion

/-! Complete mean coverage on one activity interval, for orders 59 through 349.
This is a restricted-activity theorem, not all-order unimodality. -/
namespace ForestUnimodality.BridgeActivityData.Strip012
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_valley_of_parent_mean {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤349)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : ((strip 12).mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hqs : z/(1+z)∈Set.Icc ((strip 12).qlo:ℝ) ((strip 12).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc ((29/85:ℚ):ℝ) ((89/255:ℚ):ℝ)
    norm_num
    exact hq
  by_cases hhi : hardCoreAvailableMean G S B z≤((strip 12).mhi:ℝ)
  · obtain ⟨i,hi,hpoint⟩ := (strip 12).check_sound rectangle strip012_checked hqs ⟨hm,hhi⟩
    change i∈([440,361,49,50,51] : List (Fin 558)) at hi
    have hc : i=440 ∨ i=361 ∨ i=49 ∨ i=50 ∨ i=51 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell440.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell361.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell049.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell050.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell051.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · have hp := (strip 12).parent_domain (window 12) 170
      Stage170SourceData.Window012.valid source012_checked hz hqs (le_of_not_ge hhi)
    exact Stage350ParentHandoff.no_weak_valley (window 12).parent
      k hB hG hS hp.2 hp.1 hrank hmean hk

#print axioms no_valley_of_parent_mean

theorem no_valley_of_mean_130 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤169)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage130KernelData.Cell012.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage130KernelData.Cell012.mhi:ℝ)
  · exact Stage130KernelData.Cell012.actual_no_weak_valley k hB hG hS hN hz hk
      (by simpa [Stage130KernelData.Cell012.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage130KernelData.Cell012.mhi:ℝ)=((strip 12).mlo:ℝ) := rfl
    apply no_valley_of_parent_mean k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_130

theorem no_valley_of_mean_99 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤129)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage99KernelData.Cell012.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage99KernelData.Cell012.mhi:ℝ)
  · exact Stage99KernelData.Cell012.actual_no_weak_valley k hB hG hS hN hz hk
      (by simpa [Stage99KernelData.Cell012.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage99KernelData.Cell012.mhi:ℝ)=(Stage130KernelData.Cell012.mlo:ℝ) := rfl
    apply no_valley_of_mean_130 k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_99

theorem no_valley_of_mean_80 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤98)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage80KernelData.Cell012.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage80KernelData.Cell012.mhi:ℝ)
  · exact Stage80KernelData.Cell012.actual_no_weak_valley k hB hG hS hN hz hk
      (by simpa [Stage80KernelData.Cell012.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage80KernelData.Cell012.mhi:ℝ)=(Stage99KernelData.Cell012.mlo:ℝ) := rfl
    apply no_valley_of_mean_99 k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_80

theorem no_valley_of_mean_59 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤79)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage59KernelData.Cell012.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage59KernelData.Cell012.mhi:ℝ)
  · exact Stage59KernelData.Cell012.actual_no_weak_valley k hB hG hn hN hz
      (by simpa [Stage59KernelData.Cell012.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage59KernelData.Cell012.mhi:ℝ)=(Stage99KernelData.Cell012.mlo:ℝ) := rfl
    apply no_valley_of_mean_99 k hB hG (by omega) (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms no_valley_of_mean_59

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (29/85:ℝ) (89/255:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases hn170 : 170≤S.card
  · exact Stage170Windows.Strip012.no_weak_valley k hG hn170 hN hz hq hrank hmean
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
  have hav : (k:ℝ)≤2*(89/255:ℝ)*hardCoreAvailableMean G S B z := by nlinarith
  by_cases hn130 : 130≤S.card
  · have hstage : (130:ℝ)≤S.card := by exact_mod_cast hn130
    have hnat : 33≤k := by
      by_contra h
      have hku : (k:ℝ)≤32 := by exact_mod_cast (show k≤32 by omega)
      linarith
    have hkl : (33:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_130 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage130KernelData.Cell012.mlo]
    linarith
  by_cases hn99 : 99≤S.card
  · have hstage : (99:ℝ)≤S.card := by exact_mod_cast hn99
    have hnat : 25≤k := by
      by_contra h
      have hku : (k:ℝ)≤24 := by exact_mod_cast (show k≤24 by omega)
      linarith
    have hkl : (25:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_99 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage99KernelData.Cell012.mlo]
    linarith
  by_cases hn80 : 80≤S.card
  · have hstage : (80:ℝ)≤S.card := by exact_mod_cast hn80
    have hnat : 20≤k := by
      by_contra h
      have hku : (k:ℝ)≤19 := by exact_mod_cast (show k≤19 by omega)
      linarith
    have hkl : (20:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply no_valley_of_mean_80 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage80KernelData.Cell012.mlo]
    linarith
  have hstage : (59:ℝ)≤S.card := hnR
  have hnat : 15≤k := by
    by_contra h
    have hku : (k:ℝ)≤14 := by exact_mod_cast (show k≤14 by omega)
    linarith
  have hkl : (15:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
  apply no_valley_of_mean_59 k hB hG hn (by omega) hz hk hq hrank hmean
  norm_num [Stage59KernelData.Cell012.mlo]
  linarith

#print axioms no_weak_valley
end ForestUnimodality.BridgeActivityData.Strip012
