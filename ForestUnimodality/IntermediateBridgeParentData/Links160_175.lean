import ForestUnimodality.IntermediateBridgeParent
import ForestUnimodality.IntermediateBridgeCoverData.Batch160_175

namespace ForestUnimodality.IntermediateBridgeParentData
open IntermediateBridgeCover IntermediateBridgeCoverData Stage170Geometry
universe u
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem band160_parent_link : ∃j : Fin 130,band160.parentCheck j=true := by
  exact ⟨40,by decide +kernel⟩
#print axioms band160_parent_link

theorem band161_parent_link : ∃j : Fin 130,band161.parentCheck j=true := by
  exact ⟨40,by decide +kernel⟩
#print axioms band161_parent_link

theorem band162_parent_link : ∃j : Fin 130,band162.parentCheck j=true := by
  exact ⟨40,by decide +kernel⟩
#print axioms band162_parent_link

theorem band163_parent_link : ∃j : Fin 130,band163.parentCheck j=true := by
  exact ⟨40,by decide +kernel⟩
#print axioms band163_parent_link

theorem band164_parent_link : ∃j : Fin 130,band164.parentCheck j=true := by
  exact ⟨41,by decide +kernel⟩
#print axioms band164_parent_link

theorem band165_parent_link : ∃j : Fin 130,band165.parentCheck j=true := by
  exact ⟨41,by decide +kernel⟩
#print axioms band165_parent_link

theorem band166_parent_link : ∃j : Fin 130,band166.parentCheck j=true := by
  exact ⟨41,by decide +kernel⟩
#print axioms band166_parent_link

theorem band167_parent_link : ∃j : Fin 130,band167.parentCheck j=true := by
  exact ⟨41,by decide +kernel⟩
#print axioms band167_parent_link

theorem band168_parent_link : ∃j : Fin 130,band168.parentCheck j=true := by
  exact ⟨42,by decide +kernel⟩
#print axioms band168_parent_link

theorem band169_parent_link : ∃j : Fin 130,band169.parentCheck j=true := by
  exact ⟨42,by decide +kernel⟩
#print axioms band169_parent_link

theorem band170_parent_link : ∃j : Fin 130,band170.parentCheck j=true := by
  exact ⟨42,by decide +kernel⟩
#print axioms band170_parent_link

theorem band171_parent_link : ∃j : Fin 130,band171.parentCheck j=true := by
  exact ⟨42,by decide +kernel⟩
#print axioms band171_parent_link

theorem band172_parent_link : ∃j : Fin 130,band172.parentCheck j=true := by
  exact ⟨43,by decide +kernel⟩
#print axioms band172_parent_link

theorem band173_parent_link : ∃j : Fin 130,band173.parentCheck j=true := by
  exact ⟨43,by decide +kernel⟩
#print axioms band173_parent_link

theorem band174_parent_link : ∃j : Fin 130,band174.parentCheck j=true := by
  exact ⟨43,by decide +kernel⟩
#print axioms band174_parent_link

theorem band175_parent_link : ∃j : Fin 130,band175.parentCheck j=true := by
  exact ⟨43,by decide +kernel⟩
#print axioms band175_parent_link

end ForestUnimodality.IntermediateBridgeParentData
