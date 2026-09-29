import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage130KernelData.Cell137.Conclusion
import ForestUnimodality.Stage130KernelData.Cell138.Conclusion
import ForestUnimodality.Stage130KernelData.Cell139.Conclusion
import ForestUnimodality.Stage130KernelData.Cell140.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage130_cell137 : (rectangle (130,137)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell137.interval.lo:ℝ) (Stage130KernelData.Cell137.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell137.mlo:ℝ) (Stage130KernelData.Cell137.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell137.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell137

theorem stage130_cell138 : (rectangle (130,138)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell138.interval.lo:ℝ) (Stage130KernelData.Cell138.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell138.mlo:ℝ) (Stage130KernelData.Cell138.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell138.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell138

theorem stage130_cell139 : (rectangle (130,139)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell139.interval.lo:ℝ) (Stage130KernelData.Cell139.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell139.mlo:ℝ) (Stage130KernelData.Cell139.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell139.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell139

theorem stage130_cell140 : (rectangle (130,140)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell140.interval.lo:ℝ) (Stage130KernelData.Cell140.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell140.mlo:ℝ) (Stage130KernelData.Cell140.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell140.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell140

end ForestUnimodality.IntermediateBridgeForestData
