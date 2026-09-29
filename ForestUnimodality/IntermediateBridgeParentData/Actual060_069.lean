import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170Geometry.Batch060_069
import ForestUnimodality.Stage170Windows.Strip060.Complete
import ForestUnimodality.Stage170Windows.Strip061.Complete
import ForestUnimodality.Stage170Windows.Strip062.Complete
import ForestUnimodality.Stage170Windows.Strip063.Complete
import ForestUnimodality.Stage170Windows.Strip064.Complete
import ForestUnimodality.Stage170Windows.Strip065.Complete
import ForestUnimodality.Stage170Windows.Strip066.Complete
import ForestUnimodality.Stage170Windows.Strip067.Complete
import ForestUnimodality.Stage170Windows.Strip068.Complete
import ForestUnimodality.Stage170Windows.Strip069.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent060_complete : ParentComplete.{u} 60 := by
  apply parent_complete_of_rectangles 60 strip060_checked source060_checked
  intro j hj
  change j∈([488,386,158,159,160,161,162] : List (Fin 558)) at hj
  have hc : j=488 ∨ j=386 ∨ j=158 ∨ j=159 ∨ j=160 ∨ j=161 ∨ j=162 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell488.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell386.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell158.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell159.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell160.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell161.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell162.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent060_complete

theorem parent061_complete : ParentComplete.{u} 61 := by
  apply parent_complete_of_rectangles 61 strip061_checked source061_checked
  intro j hj
  change j∈([489,386,158,159,160,161,162] : List (Fin 558)) at hj
  have hc : j=489 ∨ j=386 ∨ j=158 ∨ j=159 ∨ j=160 ∨ j=161 ∨ j=162 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell489.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell386.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell158.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell159.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell160.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell161.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell162.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent061_complete

theorem parent062_complete : ParentComplete.{u} 62 := by
  apply parent_complete_of_rectangles 62 strip062_checked source062_checked
  intro j hj
  change j∈([490,387,163,164,165,166,167] : List (Fin 558)) at hj
  have hc : j=490 ∨ j=387 ∨ j=163 ∨ j=164 ∨ j=165 ∨ j=166 ∨ j=167 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell490.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell387.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell163.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell164.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell165.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell166.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell167.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent062_complete

theorem parent063_complete : ParentComplete.{u} 63 := by
  apply parent_complete_of_rectangles 63 strip063_checked source063_checked
  intro j hj
  change j∈([491,387,163,164,165,166,167] : List (Fin 558)) at hj
  have hc : j=491 ∨ j=387 ∨ j=163 ∨ j=164 ∨ j=165 ∨ j=166 ∨ j=167 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell491.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell387.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell163.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell164.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell165.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell166.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell167.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent063_complete

theorem parent064_complete : ParentComplete.{u} 64 := by
  apply parent_complete_of_rectangles 64 strip064_checked source064_checked
  intro j hj
  change j∈([492,387,163,164,165,166,167] : List (Fin 558)) at hj
  have hc : j=492 ∨ j=387 ∨ j=163 ∨ j=164 ∨ j=165 ∨ j=166 ∨ j=167 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell492.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell387.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell163.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell164.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell165.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell166.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell167.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent064_complete

theorem parent065_complete : ParentComplete.{u} 65 := by
  apply parent_complete_of_rectangles 65 strip065_checked source065_checked
  intro j hj
  change j∈([493,387,163,164,165,166,167] : List (Fin 558)) at hj
  have hc : j=493 ∨ j=387 ∨ j=163 ∨ j=164 ∨ j=165 ∨ j=166 ∨ j=167 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell493.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell387.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell163.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell164.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell165.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell166.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell167.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent065_complete

theorem parent066_complete : ParentComplete.{u} 66 := by
  apply parent_complete_of_rectangles 66 strip066_checked source066_checked
  intro j hj
  change j∈([494,388,168,169,170,171,172] : List (Fin 558)) at hj
  have hc : j=494 ∨ j=388 ∨ j=168 ∨ j=169 ∨ j=170 ∨ j=171 ∨ j=172 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell494.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell388.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell168.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell169.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell170.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell171.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell172.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent066_complete

theorem parent067_complete : ParentComplete.{u} 67 := by
  apply parent_complete_of_rectangles 67 strip067_checked source067_checked
  intro j hj
  change j∈([495,388,168,169,170,171,172] : List (Fin 558)) at hj
  have hc : j=495 ∨ j=388 ∨ j=168 ∨ j=169 ∨ j=170 ∨ j=171 ∨ j=172 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell495.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell388.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell168.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell169.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell170.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell171.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell172.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent067_complete

theorem parent068_complete : ParentComplete.{u} 68 := by
  apply parent_complete_of_rectangles 68 strip068_checked source068_checked
  intro j hj
  change j∈([496,388,168,169,170,171,172] : List (Fin 558)) at hj
  have hc : j=496 ∨ j=388 ∨ j=168 ∨ j=169 ∨ j=170 ∨ j=171 ∨ j=172 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell496.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell388.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell168.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell169.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell170.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell171.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell172.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent068_complete

theorem parent069_complete : ParentComplete.{u} 69 := by
  apply parent_complete_of_rectangles 69 strip069_checked source069_checked
  intro j hj
  change j∈([497,388,168,169,170,171,172] : List (Fin 558)) at hj
  have hc : j=497 ∨ j=388 ∨ j=168 ∨ j=169 ∨ j=170 ∨ j=171 ∨ j=172 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell497.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell388.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell168.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell169.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell170.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell171.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell172.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent069_complete

end ForestUnimodality.IntermediateBridgeParentData
