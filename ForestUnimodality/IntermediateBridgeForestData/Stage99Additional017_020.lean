import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage99KernelData.Cell017.Conclusion
import ForestUnimodality.Stage99KernelData.Cell018.Conclusion
import ForestUnimodality.Stage99KernelData.Cell019.Conclusion
import ForestUnimodality.Stage99KernelData.Cell020.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage99_cell017 : (rectangle (99,17)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell017.interval.lo:ℝ) (Stage99KernelData.Cell017.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell017.mlo:ℝ) (Stage99KernelData.Cell017.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell017.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell017

theorem stage99_cell018 : (rectangle (99,18)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell018.interval.lo:ℝ) (Stage99KernelData.Cell018.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell018.mlo:ℝ) (Stage99KernelData.Cell018.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell018.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell018

theorem stage99_cell019 : (rectangle (99,19)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell019.interval.lo:ℝ) (Stage99KernelData.Cell019.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell019.mlo:ℝ) (Stage99KernelData.Cell019.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell019.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell019

theorem stage99_cell020 : (rectangle (99,20)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell020.interval.lo:ℝ) (Stage99KernelData.Cell020.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell020.mlo:ℝ) (Stage99KernelData.Cell020.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell020.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell020

end ForestUnimodality.IntermediateBridgeForestData
