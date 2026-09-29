import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage130KernelData.Cell164.Conclusion
import ForestUnimodality.Stage130KernelData.Cell165.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage130_cell164 : (rectangle (130,164)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell164.interval.lo:ℝ) (Stage130KernelData.Cell164.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell164.mlo:ℝ) (Stage130KernelData.Cell164.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell164.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell164

theorem stage130_cell165 : (rectangle (130,165)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell165.interval.lo:ℝ) (Stage130KernelData.Cell165.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell165.mlo:ℝ) (Stage130KernelData.Cell165.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell165.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell165

end ForestUnimodality.IntermediateBridgeForestData
