import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage99KernelData.Cell133.Conclusion
import ForestUnimodality.Stage99KernelData.Cell134.Conclusion
import ForestUnimodality.Stage99KernelData.Cell135.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage99_cell133 : (rectangle (99,133)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell133.interval.lo:ℝ) (Stage99KernelData.Cell133.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell133.mlo:ℝ) (Stage99KernelData.Cell133.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell133.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell133

theorem stage99_cell134 : (rectangle (99,134)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell134.interval.lo:ℝ) (Stage99KernelData.Cell134.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell134.mlo:ℝ) (Stage99KernelData.Cell134.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell134.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell134

theorem stage99_cell135 : (rectangle (99,135)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell135.interval.lo:ℝ) (Stage99KernelData.Cell135.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell135.mlo:ℝ) (Stage99KernelData.Cell135.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell135.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell135

end ForestUnimodality.IntermediateBridgeForestData
