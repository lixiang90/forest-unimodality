import ForestUnimodality.Stage170KernelData.Cell531.Conclusion
import ForestUnimodality.Stage170KernelData.Cell401.Conclusion
import ForestUnimodality.Stage170KernelData.Cell231.Conclusion
import ForestUnimodality.Stage170KernelData.Cell232.Conclusion
import ForestUnimodality.Stage170KernelData.Cell233.Conclusion
import ForestUnimodality.Stage170KernelData.Cell234.Conclusion
import ForestUnimodality.Stage170KernelData.Cell235.Conclusion
import ForestUnimodality.Stage170Windows.Strip103.Geometry

namespace ForestUnimodality.Stage170Windows.Strip103
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc ((49/89):ℝ) ((99/179):ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hnR : (170:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  rcases actual_finite_cover_or_no_weak_valley k hB hG hn hz hk hq hrank hmean with hf | hv
  · obtain ⟨i,hi,hpoint⟩ := hf
    have hS : 0<S.card := by omega
    have hc : i=531 ∨ i=401 ∨ i=231 ∨ i=232 ∨ i=233 ∨ i=234 ∨ i=235 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell531.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell401.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell231.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell232.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell233.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell234.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell235.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact hv

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.Strip103
