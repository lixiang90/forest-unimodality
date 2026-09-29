import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage80KernelData.Cell017.Conclusion
import ForestUnimodality.Stage80KernelData.Cell018.Conclusion
import ForestUnimodality.Stage80KernelData.Cell019.Conclusion
import ForestUnimodality.Stage80KernelData.Cell020.Conclusion
import ForestUnimodality.Stage80KernelData.Cell024.Conclusion
import ForestUnimodality.Stage80KernelData.Cell032.Conclusion
import ForestUnimodality.Stage80KernelData.Cell035.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage80_cell017 : (rectangle (80,17)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell017.interval.lo:ℝ) (Stage80KernelData.Cell017.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell017.mlo:ℝ) (Stage80KernelData.Cell017.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell017.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell017

theorem stage80_cell018 : (rectangle (80,18)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell018.interval.lo:ℝ) (Stage80KernelData.Cell018.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell018.mlo:ℝ) (Stage80KernelData.Cell018.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell018.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell018

theorem stage80_cell019 : (rectangle (80,19)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell019.interval.lo:ℝ) (Stage80KernelData.Cell019.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell019.mlo:ℝ) (Stage80KernelData.Cell019.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell019.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell019

theorem stage80_cell020 : (rectangle (80,20)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell020.interval.lo:ℝ) (Stage80KernelData.Cell020.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell020.mlo:ℝ) (Stage80KernelData.Cell020.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell020.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell020

theorem stage80_cell024 : (rectangle (80,24)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell024.interval.lo:ℝ) (Stage80KernelData.Cell024.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell024.mlo:ℝ) (Stage80KernelData.Cell024.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell024.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell024

theorem stage80_cell032 : (rectangle (80,32)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell032.interval.lo:ℝ) (Stage80KernelData.Cell032.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell032.mlo:ℝ) (Stage80KernelData.Cell032.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell032.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell032

theorem stage80_cell035 : (rectangle (80,35)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell035.interval.lo:ℝ) (Stage80KernelData.Cell035.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell035.mlo:ℝ) (Stage80KernelData.Cell035.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell035.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell035

end ForestUnimodality.IntermediateBridgeForestData
