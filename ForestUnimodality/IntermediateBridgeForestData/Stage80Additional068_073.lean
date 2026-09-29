import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage80KernelData.Cell068.Conclusion
import ForestUnimodality.Stage80KernelData.Cell069.Conclusion
import ForestUnimodality.Stage80KernelData.Cell070.Conclusion
import ForestUnimodality.Stage80KernelData.Cell072.Conclusion
import ForestUnimodality.Stage80KernelData.Cell073.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage80_cell068 : (rectangle (80,68)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell068.interval.lo:ℝ) (Stage80KernelData.Cell068.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell068.mlo:ℝ) (Stage80KernelData.Cell068.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell068.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell068

theorem stage80_cell069 : (rectangle (80,69)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell069.interval.lo:ℝ) (Stage80KernelData.Cell069.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell069.mlo:ℝ) (Stage80KernelData.Cell069.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell069.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell069

theorem stage80_cell070 : (rectangle (80,70)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell070.interval.lo:ℝ) (Stage80KernelData.Cell070.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell070.mlo:ℝ) (Stage80KernelData.Cell070.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell070.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell070

theorem stage80_cell072 : (rectangle (80,72)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell072.interval.lo:ℝ) (Stage80KernelData.Cell072.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell072.mlo:ℝ) (Stage80KernelData.Cell072.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell072.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell072

theorem stage80_cell073 : (rectangle (80,73)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell073.interval.lo:ℝ) (Stage80KernelData.Cell073.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell073.mlo:ℝ) (Stage80KernelData.Cell073.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell073.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell073

end ForestUnimodality.IntermediateBridgeForestData
