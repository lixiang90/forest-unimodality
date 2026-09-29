import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell204.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell204 : (rectangle (59,204)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell204.interval.lo:ℝ) (Stage59KernelData.Cell204.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell204.mlo:ℝ) (Stage59KernelData.Cell204.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell204.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell204

end ForestUnimodality.IntermediateBridgeForestData
