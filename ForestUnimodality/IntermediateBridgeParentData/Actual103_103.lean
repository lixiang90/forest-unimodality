import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170Geometry.Batch100_109
import ForestUnimodality.Stage170Windows.Strip103.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent103_complete : ParentComplete.{u} 103 := by
  apply parent_complete_of_rectangles 103 strip103_checked source103_checked
  intro j hj
  change j∈([531,401,231,232,233,234,235] : List (Fin 558)) at hj
  have hc : j=531 ∨ j=401 ∨ j=231 ∨ j=232 ∨ j=233 ∨ j=234 ∨ j=235 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell531.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell401.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell231.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell232.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell233.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell234.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell235.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent103_complete

end ForestUnimodality.IntermediateBridgeParentData
