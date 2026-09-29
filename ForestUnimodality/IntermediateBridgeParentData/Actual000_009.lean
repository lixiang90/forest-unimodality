import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.Stage170FirstWindow
import ForestUnimodality.Stage170Geometry.Batch000_009
import ForestUnimodality.Stage170SecondWindow
import ForestUnimodality.Stage170Windows.Strip002.Complete
import ForestUnimodality.Stage170Windows.Strip003.Complete
import ForestUnimodality.Stage170Windows.Strip004.Complete
import ForestUnimodality.Stage170Windows.Strip005.Complete
import ForestUnimodality.Stage170Windows.Strip006.Complete
import ForestUnimodality.Stage170Windows.Strip007.Complete
import ForestUnimodality.Stage170Windows.Strip008.Complete
import ForestUnimodality.Stage170Windows.Strip009.Complete

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem parent000_complete : ParentComplete.{u} 0 := by
  apply parent_complete_of_rectangles 0 strip000_checked source000_checked
  intro j hj
  change j∈([428,349,0,1,2,3] : List (Fin 558)) at hj
  have hc : j=428 ∨ j=349 ∨ j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell428.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell349.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell000.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell001.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell002.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell003.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
#print axioms parent000_complete

theorem parent001_complete : ParentComplete.{u} 1 := by
  apply parent_complete_of_rectangles 1 strip001_checked source001_checked
  intro j hj
  change j∈([429,350,4,5,6,7] : List (Fin 558)) at hj
  have hc : j=429 ∨ j=350 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell429.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell350.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell004.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell005.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell006.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
  · intro hv
    exact (not_lt_of_ge hv.1) (Stage170KernelData.Cell007.actual_left_coefficient_lt k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2)
#print axioms parent001_complete

theorem parent002_complete : ParentComplete.{u} 2 := by
  apply parent_complete_of_rectangles 2 strip002_checked source002_checked
  intro j hj
  change j∈([430,351,8,9,10,11] : List (Fin 558)) at hj
  have hc : j=430 ∨ j=351 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell430.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell351.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell008.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell009.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell010.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell011.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent002_complete

theorem parent003_complete : ParentComplete.{u} 3 := by
  apply parent_complete_of_rectangles 3 strip003_checked source003_checked
  intro j hj
  change j∈([431,352,12,13,14,15] : List (Fin 558)) at hj
  have hc : j=431 ∨ j=352 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell431.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell352.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell012.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell013.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell014.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell015.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent003_complete

theorem parent004_complete : ParentComplete.{u} 4 := by
  apply parent_complete_of_rectangles 4 strip004_checked source004_checked
  intro j hj
  change j∈([432,353,16,17,18,19,20] : List (Fin 558)) at hj
  have hc : j=432 ∨ j=353 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 ∨ j=20 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell432.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell353.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell016.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell017.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell018.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell019.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell020.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent004_complete

theorem parent005_complete : ParentComplete.{u} 5 := by
  apply parent_complete_of_rectangles 5 strip005_checked source005_checked
  intro j hj
  change j∈([433,354,21,22,23,24] : List (Fin 558)) at hj
  have hc : j=433 ∨ j=354 ∨ j=21 ∨ j=22 ∨ j=23 ∨ j=24 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell433.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell354.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell021.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell022.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell023.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell024.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent005_complete

theorem parent006_complete : ParentComplete.{u} 6 := by
  apply parent_complete_of_rectangles 6 strip006_checked source006_checked
  intro j hj
  change j∈([434,355,25,26,27,28] : List (Fin 558)) at hj
  have hc : j=434 ∨ j=355 ∨ j=25 ∨ j=26 ∨ j=27 ∨ j=28 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell434.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell355.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell025.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell026.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell027.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell028.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent006_complete

theorem parent007_complete : ParentComplete.{u} 7 := by
  apply parent_complete_of_rectangles 7 strip007_checked source007_checked
  intro j hj
  change j∈([435,356,29,30,31,32] : List (Fin 558)) at hj
  have hc : j=435 ∨ j=356 ∨ j=29 ∨ j=30 ∨ j=31 ∨ j=32 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell435.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell356.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell029.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell030.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell031.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell032.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent007_complete

theorem parent008_complete : ParentComplete.{u} 8 := by
  apply parent_complete_of_rectangles 8 strip008_checked source008_checked
  intro j hj
  change j∈([436,357,33,34,35,36] : List (Fin 558)) at hj
  have hc : j=436 ∨ j=357 ∨ j=33 ∨ j=34 ∨ j=35 ∨ j=36 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell436.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell357.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell033.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell034.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell035.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell036.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent008_complete

theorem parent009_complete : ParentComplete.{u} 9 := by
  apply parent_complete_of_rectangles 9 strip009_checked source009_checked
  intro j hj
  change j∈([437,358,37,38,39,40] : List (Fin 558)) at hj
  have hc : j=437 ∨ j=358 ∨ j=37 ∨ j=38 ∨ j=39 ∨ j=40 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro V _ G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · exact Stage170KernelData.Cell437.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell358.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell037.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell038.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell039.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
  · exact Stage170KernelData.Cell040.actual_no_weak_valley k hB hG hS hN hz hk hpoint.1 hrank hmean hpoint.2
#print axioms parent009_complete

end ForestUnimodality.IntermediateBridgeParentData
