import ForestUnimodality.Stage59KernelData.Cell001.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell001
open FiniteMarginalSupport
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem count000_checked : jointCountBound activityLower activityUpper (1) pairs ≤ countBound (1) := by
  decide +kernel
#print axioms count000_checked

theorem count_bounds_checked : ∀ j ∈ row.fixedIndices,
    jointCountBound activityLower activityUpper j pairs ≤ countBound j := by
  intro j hj
  simp [row] at hj
  rcases hj with rfl
  · exact count000_checked
#print axioms count_bounds_checked
end ForestUnimodality.Stage59KernelData.Cell001
