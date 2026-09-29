import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage99KernelData.Cell056.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage99_cell056 : (rectangle (99,56)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell056.interval.lo:ℝ) (Stage99KernelData.Cell056.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell056.mlo:ℝ) (Stage99KernelData.Cell056.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell056.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell056

end ForestUnimodality.IntermediateBridgeForestData
