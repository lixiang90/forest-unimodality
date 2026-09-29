import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell148.Conclusion
import ForestUnimodality.Stage59KernelData.Cell149.Conclusion
import ForestUnimodality.Stage59KernelData.Cell150.Conclusion
import ForestUnimodality.Stage59KernelData.Cell151.Conclusion
import ForestUnimodality.Stage59KernelData.Cell152.Conclusion
import ForestUnimodality.Stage59KernelData.Cell153.Conclusion
import ForestUnimodality.Stage59KernelData.Cell154.Conclusion
import ForestUnimodality.Stage59KernelData.Cell155.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell148 : (rectangle (59,148)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell148.interval.lo:ℝ) (Stage59KernelData.Cell148.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell148.mlo:ℝ) (Stage59KernelData.Cell148.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell148.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell148

theorem stage59_cell149 : (rectangle (59,149)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell149.interval.lo:ℝ) (Stage59KernelData.Cell149.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell149.mlo:ℝ) (Stage59KernelData.Cell149.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell149.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell149

theorem stage59_cell150 : (rectangle (59,150)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell150.interval.lo:ℝ) (Stage59KernelData.Cell150.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell150.mlo:ℝ) (Stage59KernelData.Cell150.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell150.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell150

theorem stage59_cell151 : (rectangle (59,151)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell151.interval.lo:ℝ) (Stage59KernelData.Cell151.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell151.mlo:ℝ) (Stage59KernelData.Cell151.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell151.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell151

theorem stage59_cell152 : (rectangle (59,152)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell152.interval.lo:ℝ) (Stage59KernelData.Cell152.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell152.mlo:ℝ) (Stage59KernelData.Cell152.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell152.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell152

theorem stage59_cell153 : (rectangle (59,153)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell153.interval.lo:ℝ) (Stage59KernelData.Cell153.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell153.mlo:ℝ) (Stage59KernelData.Cell153.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell153.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell153

theorem stage59_cell154 : (rectangle (59,154)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell154.interval.lo:ℝ) (Stage59KernelData.Cell154.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell154.mlo:ℝ) (Stage59KernelData.Cell154.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell154.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell154

theorem stage59_cell155 : (rectangle (59,155)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell155.interval.lo:ℝ) (Stage59KernelData.Cell155.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell155.mlo:ℝ) (Stage59KernelData.Cell155.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell155.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell155

end ForestUnimodality.IntermediateBridgeForestData
