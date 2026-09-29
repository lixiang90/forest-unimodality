import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage130KernelData.Cell113.Conclusion
import ForestUnimodality.Stage130KernelData.Cell114.Conclusion
import ForestUnimodality.Stage130KernelData.Cell115.Conclusion
import ForestUnimodality.Stage130KernelData.Cell116.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage130_cell113 : (rectangle (130,113)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell113.interval.lo:ℝ) (Stage130KernelData.Cell113.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell113.mlo:ℝ) (Stage130KernelData.Cell113.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell113.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell113

theorem stage130_cell114 : (rectangle (130,114)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell114.interval.lo:ℝ) (Stage130KernelData.Cell114.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell114.mlo:ℝ) (Stage130KernelData.Cell114.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell114.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell114

theorem stage130_cell115 : (rectangle (130,115)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell115.interval.lo:ℝ) (Stage130KernelData.Cell115.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell115.mlo:ℝ) (Stage130KernelData.Cell115.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell115.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell115

theorem stage130_cell116 : (rectangle (130,116)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell116.interval.lo:ℝ) (Stage130KernelData.Cell116.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell116.mlo:ℝ) (Stage130KernelData.Cell116.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell116.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell116

end ForestUnimodality.IntermediateBridgeForestData
