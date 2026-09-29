import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170Geometry.Batch050_059
import ForestUnimodality.Stage170Windows.Strip050.Complete
import ForestUnimodality.Stage170Windows.Strip051.Complete
import ForestUnimodality.Stage170Windows.Strip052.Complete
import ForestUnimodality.Stage170Windows.Strip053.Complete
import ForestUnimodality.Stage170Windows.Strip054.Complete
import ForestUnimodality.Stage170Windows.Strip055.Complete
import ForestUnimodality.Stage170Windows.Strip056.Complete
import ForestUnimodality.Stage170Windows.Strip057.Complete
import ForestUnimodality.Stage170Windows.Strip058.Complete
import ForestUnimodality.Stage170Windows.Strip059.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent050_complete : ParentComplete.{u} 50 := by
  apply parent_complete_of_rectangles 50 strip050_checked source050_checked
  intro j hj
  change j∈([478,384,148,149,150,151,152] : List (Fin 558)) at hj
  have hc : j=478 ∨ j=384 ∨ j=148 ∨ j=149 ∨ j=150 ∨ j=151 ∨ j=152 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell478.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell384.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell148.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell149.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell150.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell151.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell152.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent050_complete

theorem parent051_complete : ParentComplete.{u} 51 := by
  apply parent_complete_of_rectangles 51 strip051_checked source051_checked
  intro j hj
  change j∈([479,384,148,149,150,151,152] : List (Fin 558)) at hj
  have hc : j=479 ∨ j=384 ∨ j=148 ∨ j=149 ∨ j=150 ∨ j=151 ∨ j=152 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell479.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell384.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell148.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell149.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell150.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell151.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell152.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent051_complete

theorem parent052_complete : ParentComplete.{u} 52 := by
  apply parent_complete_of_rectangles 52 strip052_checked source052_checked
  intro j hj
  change j∈([480,384,148,149,150,151,152] : List (Fin 558)) at hj
  have hc : j=480 ∨ j=384 ∨ j=148 ∨ j=149 ∨ j=150 ∨ j=151 ∨ j=152 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell480.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell384.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell148.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell149.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell150.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell151.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell152.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent052_complete

theorem parent053_complete : ParentComplete.{u} 53 := by
  apply parent_complete_of_rectangles 53 strip053_checked source053_checked
  intro j hj
  change j∈([481,384,148,149,150,151,152] : List (Fin 558)) at hj
  have hc : j=481 ∨ j=384 ∨ j=148 ∨ j=149 ∨ j=150 ∨ j=151 ∨ j=152 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell481.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell384.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell148.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell149.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell150.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell151.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell152.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent053_complete

theorem parent054_complete : ParentComplete.{u} 54 := by
  apply parent_complete_of_rectangles 54 strip054_checked source054_checked
  intro j hj
  change j∈([482,385,153,154,155,156,157] : List (Fin 558)) at hj
  have hc : j=482 ∨ j=385 ∨ j=153 ∨ j=154 ∨ j=155 ∨ j=156 ∨ j=157 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell482.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell385.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell153.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell154.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell155.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell156.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell157.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent054_complete

theorem parent055_complete : ParentComplete.{u} 55 := by
  apply parent_complete_of_rectangles 55 strip055_checked source055_checked
  intro j hj
  change j∈([483,385,153,154,155,156,157] : List (Fin 558)) at hj
  have hc : j=483 ∨ j=385 ∨ j=153 ∨ j=154 ∨ j=155 ∨ j=156 ∨ j=157 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell483.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell385.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell153.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell154.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell155.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell156.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell157.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent055_complete

theorem parent056_complete : ParentComplete.{u} 56 := by
  apply parent_complete_of_rectangles 56 strip056_checked source056_checked
  intro j hj
  change j∈([484,385,153,154,155,156,157] : List (Fin 558)) at hj
  have hc : j=484 ∨ j=385 ∨ j=153 ∨ j=154 ∨ j=155 ∨ j=156 ∨ j=157 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell484.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell385.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell153.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell154.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell155.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell156.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell157.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent056_complete

theorem parent057_complete : ParentComplete.{u} 57 := by
  apply parent_complete_of_rectangles 57 strip057_checked source057_checked
  intro j hj
  change j∈([485,385,153,154,155,156,157] : List (Fin 558)) at hj
  have hc : j=485 ∨ j=385 ∨ j=153 ∨ j=154 ∨ j=155 ∨ j=156 ∨ j=157 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell485.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell385.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell153.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell154.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell155.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell156.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell157.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent057_complete

theorem parent058_complete : ParentComplete.{u} 58 := by
  apply parent_complete_of_rectangles 58 strip058_checked source058_checked
  intro j hj
  change j∈([486,386,158,159,160,161,162] : List (Fin 558)) at hj
  have hc : j=486 ∨ j=386 ∨ j=158 ∨ j=159 ∨ j=160 ∨ j=161 ∨ j=162 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell486.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell386.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell158.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell159.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell160.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell161.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell162.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent058_complete

theorem parent059_complete : ParentComplete.{u} 59 := by
  apply parent_complete_of_rectangles 59 strip059_checked source059_checked
  intro j hj
  change j∈([487,386,158,159,160,161,162] : List (Fin 558)) at hj
  have hc : j=487 ∨ j=386 ∨ j=158 ∨ j=159 ∨ j=160 ∨ j=161 ∨ j=162 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell487.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell386.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell158.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell159.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell160.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell161.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell162.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent059_complete

end ForestUnimodality.IntermediateBridgeParentData
