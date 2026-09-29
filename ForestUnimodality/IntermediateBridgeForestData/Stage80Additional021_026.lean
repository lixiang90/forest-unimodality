import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage80KernelData.Cell021.Conclusion
import ForestUnimodality.Stage80KernelData.Cell023.Conclusion
import ForestUnimodality.Stage80KernelData.Cell025.Conclusion
import ForestUnimodality.Stage80KernelData.Cell026.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage80_cell021 : (rectangle (80,21)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell021.interval.lo:ℝ) (Stage80KernelData.Cell021.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell021.mlo:ℝ) (Stage80KernelData.Cell021.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell021.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell021

theorem stage80_cell023 : (rectangle (80,23)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell023.interval.lo:ℝ) (Stage80KernelData.Cell023.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell023.mlo:ℝ) (Stage80KernelData.Cell023.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell023.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell023

theorem stage80_cell025 : (rectangle (80,25)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell025.interval.lo:ℝ) (Stage80KernelData.Cell025.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell025.mlo:ℝ) (Stage80KernelData.Cell025.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell025.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell025

theorem stage80_cell026 : (rectangle (80,26)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell026.interval.lo:ℝ) (Stage80KernelData.Cell026.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell026.mlo:ℝ) (Stage80KernelData.Cell026.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell026.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell026

end ForestUnimodality.IntermediateBridgeForestData
