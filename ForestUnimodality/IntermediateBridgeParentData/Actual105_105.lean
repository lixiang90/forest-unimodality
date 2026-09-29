import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170Geometry.Batch100_109
import ForestUnimodality.Stage170Windows.Strip105.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent105_complete : ParentComplete.{u} 105 := by
  apply parent_complete_of_rectangles 105 strip105_checked source105_checked
  intro j hj
  change j∈([533,403,241,242,243,244] : List (Fin 558)) at hj
  have hc : j=533 ∨ j=403 ∨ j=241 ∨ j=242 ∨ j=243 ∨ j=244 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell533.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell403.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell241.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell242.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell243.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell244.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent105_complete

end ForestUnimodality.IntermediateBridgeParentData
