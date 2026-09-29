import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.IntermediateBridgeCoverData.Batch608_615

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band608_parent_link : ∃j : Fin 130,band608.parentCheck j=true := by
  exact ⟨128,by decide +kernel⟩
#print axioms band608_parent_link

theorem band609_parent_link : ∃j : Fin 130,band609.parentCheck j=true := by
  exact ⟨128,by decide +kernel⟩
#print axioms band609_parent_link

theorem band610_parent_link : ∃j : Fin 130,band610.parentCheck j=true := by
  exact ⟨128,by decide +kernel⟩
#print axioms band610_parent_link

theorem band611_parent_link : ∃j : Fin 130,band611.parentCheck j=true := by
  exact ⟨128,by decide +kernel⟩
#print axioms band611_parent_link

theorem band612_parent_link : ∃j : Fin 130,band612.parentCheck j=true := by
  exact ⟨129,by decide +kernel⟩
#print axioms band612_parent_link

theorem band613_parent_link : ∃j : Fin 130,band613.parentCheck j=true := by
  exact ⟨129,by decide +kernel⟩
#print axioms band613_parent_link

theorem band614_parent_link : ∃j : Fin 130,band614.parentCheck j=true := by
  exact ⟨129,by decide +kernel⟩
#print axioms band614_parent_link

theorem band615_parent_link : ∃j : Fin 130,band615.parentCheck j=true := by
  exact ⟨129,by decide +kernel⟩
#print axioms band615_parent_link

end ForestUnimodality.IntermediateBridgeParentData
