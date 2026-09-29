import ForestUnimodality.Stage59KernelData.Cell180.Parameters

namespace ForestUnimodality.Stage59KernelData.Cell180
open FiniteMarginalSupport
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem count000_checked : jointCountBound activityLower activityUpper (-1) pairs ≤ countBound (-1) := by
  decide +kernel
#print axioms count000_checked

theorem count001_checked : jointCountBound activityLower activityUpper (0) pairs ≤ countBound (0) := by
  decide +kernel
#print axioms count001_checked

theorem count002_checked : jointCountBound activityLower activityUpper (1) pairs ≤ countBound (1) := by
  decide +kernel
#print axioms count002_checked

theorem count003_checked : jointCountBound activityLower activityUpper (2) pairs ≤ countBound (2) := by
  decide +kernel
#print axioms count003_checked

theorem count004_checked : jointCountBound activityLower activityUpper (3) pairs ≤ countBound (3) := by
  decide +kernel
#print axioms count004_checked

theorem count_bounds_checked : ∀ j ∈ row.fixedIndices,
    jointCountBound activityLower activityUpper j pairs ≤ countBound j := by
  intro j hj
  simp [row] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact count000_checked
  · exact count001_checked
  · exact count002_checked
  · exact count003_checked
  · exact count004_checked
#print axioms count_bounds_checked
end ForestUnimodality.Stage59KernelData.Cell180
