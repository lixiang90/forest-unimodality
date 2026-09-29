import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170Geometry.Batch120_129
import ForestUnimodality.Stage170Windows.Strip128.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent128_complete : ParentComplete.{u} 128 := by
  apply parent_complete_of_rectangles 128 strip128_checked source128_checked
  intro j hj
  change j∈([556,426,341,342,343,344] : List (Fin 558)) at hj
  have hc : j=556 ∨ j=426 ∨ j=341 ∨ j=342 ∨ j=343 ∨ j=344 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell556.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell426.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell341.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell342.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell343.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell344.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent128_complete

end ForestUnimodality.IntermediateBridgeParentData
