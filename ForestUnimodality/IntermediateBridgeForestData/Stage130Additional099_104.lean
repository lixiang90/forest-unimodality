import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage130KernelData.Cell099.Conclusion
import ForestUnimodality.Stage130KernelData.Cell100.Conclusion
import ForestUnimodality.Stage130KernelData.Cell101.Conclusion
import ForestUnimodality.Stage130KernelData.Cell102.Conclusion
import ForestUnimodality.Stage130KernelData.Cell103.Conclusion
import ForestUnimodality.Stage130KernelData.Cell104.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage130_cell099 : (rectangle (130,99)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell099.interval.lo:ℝ) (Stage130KernelData.Cell099.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell099.mlo:ℝ) (Stage130KernelData.Cell099.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell099.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell099

theorem stage130_cell100 : (rectangle (130,100)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell100.interval.lo:ℝ) (Stage130KernelData.Cell100.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell100.mlo:ℝ) (Stage130KernelData.Cell100.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell100.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell100

theorem stage130_cell101 : (rectangle (130,101)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell101.interval.lo:ℝ) (Stage130KernelData.Cell101.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell101.mlo:ℝ) (Stage130KernelData.Cell101.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell101.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell101

theorem stage130_cell102 : (rectangle (130,102)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell102.interval.lo:ℝ) (Stage130KernelData.Cell102.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell102.mlo:ℝ) (Stage130KernelData.Cell102.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell102.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell102

theorem stage130_cell103 : (rectangle (130,103)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell103.interval.lo:ℝ) (Stage130KernelData.Cell103.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell103.mlo:ℝ) (Stage130KernelData.Cell103.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell103.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell103

theorem stage130_cell104 : (rectangle (130,104)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell104.interval.lo:ℝ) (Stage130KernelData.Cell104.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell104.mlo:ℝ) (Stage130KernelData.Cell104.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell104.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell104

end ForestUnimodality.IntermediateBridgeForestData
