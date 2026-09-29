import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell170.Conclusion
import ForestUnimodality.Stage59KernelData.Cell171.Conclusion
import ForestUnimodality.Stage59KernelData.Cell172.Conclusion
import ForestUnimodality.Stage59KernelData.Cell173.Conclusion
import ForestUnimodality.Stage59KernelData.Cell174.Conclusion
import ForestUnimodality.Stage59KernelData.Cell175.Conclusion
import ForestUnimodality.Stage59KernelData.Cell176.Conclusion
import ForestUnimodality.Stage59KernelData.Cell177.Conclusion
import ForestUnimodality.Stage59KernelData.Cell178.Conclusion
import ForestUnimodality.Stage59KernelData.Cell183.Conclusion
import ForestUnimodality.Stage59KernelData.Cell184.Conclusion
import ForestUnimodality.Stage59KernelData.Cell185.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell170 : (rectangle (59,170)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell170.interval.lo:ℝ) (Stage59KernelData.Cell170.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell170.mlo:ℝ) (Stage59KernelData.Cell170.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell170.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell170

theorem stage59_cell171 : (rectangle (59,171)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell171.interval.lo:ℝ) (Stage59KernelData.Cell171.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell171.mlo:ℝ) (Stage59KernelData.Cell171.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell171.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell171

theorem stage59_cell172 : (rectangle (59,172)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell172.interval.lo:ℝ) (Stage59KernelData.Cell172.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell172.mlo:ℝ) (Stage59KernelData.Cell172.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell172.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell172

theorem stage59_cell173 : (rectangle (59,173)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell173.interval.lo:ℝ) (Stage59KernelData.Cell173.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell173.mlo:ℝ) (Stage59KernelData.Cell173.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell173.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell173

theorem stage59_cell174 : (rectangle (59,174)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell174.interval.lo:ℝ) (Stage59KernelData.Cell174.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell174.mlo:ℝ) (Stage59KernelData.Cell174.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell174.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell174

theorem stage59_cell175 : (rectangle (59,175)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell175.interval.lo:ℝ) (Stage59KernelData.Cell175.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell175.mlo:ℝ) (Stage59KernelData.Cell175.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell175.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell175

theorem stage59_cell176 : (rectangle (59,176)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell176.interval.lo:ℝ) (Stage59KernelData.Cell176.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell176.mlo:ℝ) (Stage59KernelData.Cell176.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell176.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell176

theorem stage59_cell177 : (rectangle (59,177)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell177.interval.lo:ℝ) (Stage59KernelData.Cell177.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell177.mlo:ℝ) (Stage59KernelData.Cell177.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell177.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell177

theorem stage59_cell178 : (rectangle (59,178)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell178.interval.lo:ℝ) (Stage59KernelData.Cell178.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell178.mlo:ℝ) (Stage59KernelData.Cell178.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell178.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell178

theorem stage59_cell183 : (rectangle (59,183)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell183.interval.lo:ℝ) (Stage59KernelData.Cell183.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell183.mlo:ℝ) (Stage59KernelData.Cell183.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell183.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell183

theorem stage59_cell184 : (rectangle (59,184)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell184.interval.lo:ℝ) (Stage59KernelData.Cell184.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell184.mlo:ℝ) (Stage59KernelData.Cell184.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell184.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell184

theorem stage59_cell185 : (rectangle (59,185)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell185.interval.lo:ℝ) (Stage59KernelData.Cell185.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell185.mlo:ℝ) (Stage59KernelData.Cell185.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell185.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell185

end ForestUnimodality.IntermediateBridgeForestData
