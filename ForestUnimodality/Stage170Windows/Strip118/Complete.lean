import ForestUnimodality.Stage170KernelData.Cell546.Conclusion
import ForestUnimodality.Stage170KernelData.Cell416.Conclusion
import ForestUnimodality.Stage170KernelData.Cell299.Conclusion
import ForestUnimodality.Stage170KernelData.Cell300.Conclusion
import ForestUnimodality.Stage170KernelData.Cell301.Conclusion
import ForestUnimodality.Stage170KernelData.Cell302.Conclusion
import ForestUnimodality.Stage170KernelData.Cell303.Conclusion
import ForestUnimodality.Stage170Windows.Strip118.Geometry

namespace ForestUnimodality.Stage170Windows.Strip118
open Stage170Geometry
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc ((63/103):ℝ) ((129/209):ℝ))
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
    have hc : i=546 ∨ i=416 ∨ i=299 ∨ i=300 ∨ i=301 ∨ i=302 ∨ i=303 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Stage170KernelData.Cell546.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell416.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell299.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell300.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell301.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell302.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
    · exact Stage170KernelData.Cell303.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact hv

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.Strip118
