import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell047.Conclusion
import ForestUnimodality.Stage59KernelData.Cell048.Conclusion
import ForestUnimodality.Stage59KernelData.Cell049.Conclusion
import ForestUnimodality.Stage59KernelData.Cell050.Conclusion
import ForestUnimodality.Stage59KernelData.Cell051.Conclusion
import ForestUnimodality.Stage59KernelData.Cell052.Conclusion
import ForestUnimodality.Stage59KernelData.Cell053.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell047 : (rectangle (59,47)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell047.interval.lo:ℝ) (Stage59KernelData.Cell047.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell047.mlo:ℝ) (Stage59KernelData.Cell047.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell047.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell047

theorem stage59_cell048 : (rectangle (59,48)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell048.interval.lo:ℝ) (Stage59KernelData.Cell048.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell048.mlo:ℝ) (Stage59KernelData.Cell048.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell048.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell048

theorem stage59_cell049 : (rectangle (59,49)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell049.interval.lo:ℝ) (Stage59KernelData.Cell049.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell049.mlo:ℝ) (Stage59KernelData.Cell049.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell049.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell049

theorem stage59_cell050 : (rectangle (59,50)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell050.interval.lo:ℝ) (Stage59KernelData.Cell050.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell050.mlo:ℝ) (Stage59KernelData.Cell050.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell050.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell050

theorem stage59_cell051 : (rectangle (59,51)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell051.interval.lo:ℝ) (Stage59KernelData.Cell051.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell051.mlo:ℝ) (Stage59KernelData.Cell051.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell051.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell051

theorem stage59_cell052 : (rectangle (59,52)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell052.interval.lo:ℝ) (Stage59KernelData.Cell052.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell052.mlo:ℝ) (Stage59KernelData.Cell052.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell052.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell052

theorem stage59_cell053 : (rectangle (59,53)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell053.interval.lo:ℝ) (Stage59KernelData.Cell053.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell053.mlo:ℝ) (Stage59KernelData.Cell053.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell053.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell053

end ForestUnimodality.IntermediateBridgeForestData
