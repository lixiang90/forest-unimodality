import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage80KernelData.Cell048.Conclusion
import ForestUnimodality.Stage80KernelData.Cell053.Conclusion
import ForestUnimodality.Stage80KernelData.Cell062.Conclusion
import ForestUnimodality.Stage80KernelData.Cell063.Conclusion
import ForestUnimodality.Stage80KernelData.Cell076.Conclusion
import ForestUnimodality.Stage80KernelData.Cell077.Conclusion
import ForestUnimodality.Stage80KernelData.Cell221.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage80_cell048 : (rectangle (80,48)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell048.interval.lo:ℝ) (Stage80KernelData.Cell048.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell048.mlo:ℝ) (Stage80KernelData.Cell048.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell048.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell048

theorem stage80_cell053 : (rectangle (80,53)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell053.interval.lo:ℝ) (Stage80KernelData.Cell053.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell053.mlo:ℝ) (Stage80KernelData.Cell053.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell053.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell053

theorem stage80_cell062 : (rectangle (80,62)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell062.interval.lo:ℝ) (Stage80KernelData.Cell062.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell062.mlo:ℝ) (Stage80KernelData.Cell062.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell062.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell062

theorem stage80_cell063 : (rectangle (80,63)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 80≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell063.interval.lo:ℝ) (Stage80KernelData.Cell063.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell063.mlo:ℝ) (Stage80KernelData.Cell063.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell063.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell063

theorem stage80_cell076 : (rectangle (80,76)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell076.interval.lo:ℝ) (Stage80KernelData.Cell076.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell076.mlo:ℝ) (Stage80KernelData.Cell076.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell076.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell076

theorem stage80_cell077 : (rectangle (80,77)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell077.interval.lo:ℝ) (Stage80KernelData.Cell077.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell077.mlo:ℝ) (Stage80KernelData.Cell077.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell077.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell077

theorem stage80_cell221 : (rectangle (80,221)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤98 ∧
      z/(1+z)∈Set.Icc (Stage80KernelData.Cell221.interval.lo:ℝ) (Stage80KernelData.Cell221.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage80KernelData.Cell221.mlo:ℝ) (Stage80KernelData.Cell221.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage80KernelData.Cell221.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage80_cell221

end ForestUnimodality.IntermediateBridgeForestData
