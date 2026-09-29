import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell186.Conclusion
import ForestUnimodality.Stage59KernelData.Cell187.Conclusion
import ForestUnimodality.Stage59KernelData.Cell188.Conclusion
import ForestUnimodality.Stage59KernelData.Cell189.Conclusion
import ForestUnimodality.Stage59KernelData.Cell190.Conclusion
import ForestUnimodality.Stage59KernelData.Cell191.Conclusion
import ForestUnimodality.Stage59KernelData.Cell192.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell186 : (rectangle (59,186)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell186.interval.lo:ℝ) (Stage59KernelData.Cell186.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell186.mlo:ℝ) (Stage59KernelData.Cell186.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell186.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell186

theorem stage59_cell187 : (rectangle (59,187)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell187.interval.lo:ℝ) (Stage59KernelData.Cell187.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell187.mlo:ℝ) (Stage59KernelData.Cell187.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell187.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell187

theorem stage59_cell188 : (rectangle (59,188)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell188.interval.lo:ℝ) (Stage59KernelData.Cell188.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell188.mlo:ℝ) (Stage59KernelData.Cell188.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell188.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell188

theorem stage59_cell189 : (rectangle (59,189)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell189.interval.lo:ℝ) (Stage59KernelData.Cell189.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell189.mlo:ℝ) (Stage59KernelData.Cell189.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell189.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell189

theorem stage59_cell190 : (rectangle (59,190)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell190.interval.lo:ℝ) (Stage59KernelData.Cell190.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell190.mlo:ℝ) (Stage59KernelData.Cell190.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell190.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell190

theorem stage59_cell191 : (rectangle (59,191)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell191.interval.lo:ℝ) (Stage59KernelData.Cell191.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell191.mlo:ℝ) (Stage59KernelData.Cell191.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell191.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell191

theorem stage59_cell192 : (rectangle (59,192)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell192.interval.lo:ℝ) (Stage59KernelData.Cell192.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell192.mlo:ℝ) (Stage59KernelData.Cell192.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell192.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell192

end ForestUnimodality.IntermediateBridgeForestData
