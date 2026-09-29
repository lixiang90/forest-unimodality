import ForestUnimodality.Stage170SecondWindow
import ForestUnimodality.Stage130KernelData.Cell001.Conclusion
import ForestUnimodality.Stage99KernelData.Cell001.Conclusion
import ForestUnimodality.Stage80KernelData.Cell001.Conclusion
import ForestUnimodality.Stage59KernelData.Cell001.Conclusion

/-! The whole second activity interval for orders 59 through 349.
Available-mean rectangle hypotheses are discharged by graph inequalities,
integer rank bounds, exact endpoints, and the all-order parent handoff. -/
namespace ForestUnimodality.BridgeSecondActivity
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem small_left {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59≤S.card) (hN : S.card≤79) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (Stage59KernelData.Cell001.interval.lo:ℝ)
      (Stage59KernelData.Cell001.interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell001.mlo:ℝ)
      (Stage59KernelData.Cell001.mhi:ℝ)) :
    countIndependent G S (k-1)<countIndependent G S k := by
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  have hp := Stage59KernelData.Cell001.actual_kernel_positive k hB hG hn hN hz hq hrank hmean hm
  rw [averagedBinomialKernel_eq G S B hB.subset hB.independent hz _ _ _ hk] at hp
  have hl : 0<4*tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by
    simpa only [Stage59KernelData.Cell001.row,Rat.cast_ofNat,Rat.cast_zero,zero_mul,add_zero] using hp
  exact ProbabilityDirectionBudget.left_coefficient_lt (countIndependent G S)
    hz (partitionFunction_pos G S hz.le) hk (by linarith)

#print axioms small_left

theorem left_of_parent_mean {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤349)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : ((strip 1).mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)<countIndependent G S k := by
  have hqs : z/(1+z)∈Set.Icc ((strip 1).qlo:ℝ) ((strip 1).qhi:ℝ) := by
    change z/(1+z)∈Set.Icc ((9/35:ℚ):ℝ) ((37/140:ℚ):ℝ)
    norm_num
    exact hq
  by_cases hhi : hardCoreAvailableMean G S B z≤((strip 1).mhi:ℝ)
  · obtain ⟨i,hi,hpoint⟩ := (strip 1).check_sound rectangle strip001_checked hqs ⟨hm,hhi⟩
    change i∈([429,350,4,5,6,7] : List (Fin 558)) at hi
    have hc : i=429 ∨ i=350 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell429.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell350.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell004.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell005.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell006.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell007.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · have hp := (strip 1).parent_domain (window 1) 170
      Stage170SourceData.Window001.valid source001_checked hz hqs (le_of_not_ge hhi)
    apply Stage350PlainAllOrders.actual_left_coefficient_lt 0 (by decide +kernel)
      k hB hG hS _ _ hrank hmean hk
    · rw [Stage350PlainAllOrders.source_start_eq]
      exact hp.2
    · change z∈Set.Icc (1/3:ℝ) (2/5:ℝ)
      have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
      have hu := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
      constructor <;> linarith

#print axioms left_of_parent_mean

theorem left_of_mean_130 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤169)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage130KernelData.Cell001.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage130KernelData.Cell001.mhi:ℝ)
  · exact Stage130KernelData.Cell001.actual_left_coefficient_lt k hB hG hS hN hz hk
      (by simpa [Stage130KernelData.Cell001.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage130KernelData.Cell001.mhi:ℝ)=((strip 1).mlo:ℝ) := rfl
    apply left_of_parent_mean k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms left_of_mean_130

theorem left_of_mean_99 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤129)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage99KernelData.Cell001.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage99KernelData.Cell001.mhi:ℝ)
  · exact Stage99KernelData.Cell001.actual_left_coefficient_lt k hB hG hS hN hz hk
      (by simpa [Stage99KernelData.Cell001.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage99KernelData.Cell001.mhi:ℝ)=(Stage130KernelData.Cell001.mlo:ℝ) := rfl
    apply left_of_mean_130 k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms left_of_mean_99

theorem left_of_mean_80 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤98)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage80KernelData.Cell001.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage80KernelData.Cell001.mhi:ℝ)
  · exact Stage80KernelData.Cell001.actual_left_coefficient_lt k hB hG hS hN hz hk
      (by simpa [Stage80KernelData.Cell001.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage80KernelData.Cell001.mhi:ℝ)=(Stage99KernelData.Cell001.mlo:ℝ) := rfl
    apply left_of_mean_99 k hB hG hS (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms left_of_mean_80

theorem left_of_mean_59 {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤79)
    (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hm : (Stage59KernelData.Cell001.mlo:ℝ)≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases hhi : hardCoreAvailableMean G S B z≤(Stage59KernelData.Cell001.mhi:ℝ)
  · exact small_left k hB hG hn hN hz
      (by simpa [Stage59KernelData.Cell001.interval] using hq) hrank hmean ⟨hm,hhi⟩
  · have he : (Stage59KernelData.Cell001.mhi:ℝ)=(Stage99KernelData.Cell001.mlo:ℝ) := rfl
    apply left_of_mean_99 k hB hG (by omega) (by omega) hz hk hq hrank hmean
    rw [←he]
    exact le_of_not_ge hhi

#print axioms left_of_mean_59

theorem rank_le_available {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)≤(37/140:ℝ)) (hmean : hardCoreMean G S z=k) :
    (k:ℝ)≤2*(37/140:ℝ)*hardCoreAvailableMean G S B z := by
  have hh := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,
    hmean] at hh
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hmul := mul_le_mul_of_nonneg_right hq hm
  nlinarith

theorem left_window_coefficient_lt {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    countIndependent G S (k-1)<countIndependent G S k := by
  by_cases hn170 : 170≤S.card
  · exact Stage170SecondWindow.left_window_coefficient_lt k hG hn170 hN hz hq hrank hmean
  obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hS : 0<S.card := by omega
  have hkr : (S.card:ℝ)/4≤(k:ℝ) := by simpa only [hmean] using hrank
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  have hav := rank_le_available k hB hG hz hq.2 hmean
  by_cases hn130 : 130≤S.card
  · have hn' : (130:ℝ)≤S.card := by exact_mod_cast hn130
    have hnat : 33≤k := by
      by_contra h
      have hk' : (k:ℝ)≤32 := by exact_mod_cast (show k≤32 by omega)
      linarith
    have hk' : (33:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply left_of_mean_130 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage130KernelData.Cell001.mlo]
    linarith
  by_cases hn99 : 99≤S.card
  · have hn' : (99:ℝ)≤S.card := by exact_mod_cast hn99
    have hnat : 25≤k := by
      by_contra h
      have hk' : (k:ℝ)≤24 := by exact_mod_cast (show k≤24 by omega)
      linarith
    have hk' : (25:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
    apply left_of_mean_99 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage99KernelData.Cell001.mlo]
    linarith
  by_cases hn80 : 80≤S.card
  · have hn' : (80:ℝ)≤S.card := by exact_mod_cast hn80
    apply left_of_mean_80 k hB hG hS (by omega) hz hk hq hrank hmean
    norm_num [Stage80KernelData.Cell001.mlo]
    linarith
  have hnat : 15≤k := by
    by_contra h
    have hk' : (k:ℝ)≤14 := by exact_mod_cast (show k≤14 by omega)
    linarith
  have hk' : (15:ℝ)≤(k:ℝ) := by exact_mod_cast hnat
  apply left_of_mean_59 k hB hG hn (by omega) hz hk hq hrank hmean
  norm_num [Stage59KernelData.Cell001.mlo]
  linarith

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (9/35:ℝ) (37/140:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  have hh := left_window_coefficient_lt k hG hn hN hz hq hrank hmean
  rintro ⟨hl,_⟩
  exact (not_le_of_gt hh) hl

#print axioms rank_le_available
#print axioms left_window_coefficient_lt
#print axioms no_weak_valley
end ForestUnimodality.BridgeSecondActivity
