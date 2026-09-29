import ForestUnimodality.Stage59KernelData.Cell004.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell004
open FiniteMarginalSupport
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem count_bounds_checked : ∀ j ∈ row.fixedIndices,
    jointCountBound activityLower activityUpper j pairs ≤ countBound j := by
  intro j hj
  simp [row] at hj
#print axioms count_bounds_checked
end ForestUnimodality.Stage59KernelData.Cell004
