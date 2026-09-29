import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell080.Conclusion
import ForestUnimodality.Stage59KernelData.Cell081.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell080 : (rectangle (59,80)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell080.interval.lo:ℝ) (Stage59KernelData.Cell080.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell080.mlo:ℝ) (Stage59KernelData.Cell080.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell080.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell080

theorem stage59_cell081 : (rectangle (59,81)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell081.interval.lo:ℝ) (Stage59KernelData.Cell081.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell081.mlo:ℝ) (Stage59KernelData.Cell081.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell081.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell081

end ForestUnimodality.IntermediateBridgeForestData
