import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage80KernelData.Cell137.Conclusion
import ForestUnimodality.Stage80KernelData.Cell141.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage80_cell137 : (rectangle (80,137)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell137.interval.lo:ℝ) (Stage80KernelData.Cell137.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell137.mlo:ℝ) (Stage80KernelData.Cell137.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell137.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell137

theorem stage80_cell141 : (rectangle (80,141)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell141.interval.lo:ℝ) (Stage80KernelData.Cell141.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell141.mlo:ℝ) (Stage80KernelData.Cell141.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell141.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell141

end ForestUnimodality.IntermediateBridgeForestData
