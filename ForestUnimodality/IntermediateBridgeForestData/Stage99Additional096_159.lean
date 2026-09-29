import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage99KernelData.Cell096.Conclusion
import ForestUnimodality.Stage99KernelData.Cell097.Conclusion
import ForestUnimodality.Stage99KernelData.Cell157.Conclusion
import ForestUnimodality.Stage99KernelData.Cell159.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage99_cell096 : (rectangle (99,96)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell096.interval.lo:ℝ) (Stage99KernelData.Cell096.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell096.mlo:ℝ) (Stage99KernelData.Cell096.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell096.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell096

theorem stage99_cell097 : (rectangle (99,97)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell097.interval.lo:ℝ) (Stage99KernelData.Cell097.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell097.mlo:ℝ) (Stage99KernelData.Cell097.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell097.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell097

theorem stage99_cell157 : (rectangle (99,157)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell157.interval.lo:ℝ) (Stage99KernelData.Cell157.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell157.mlo:ℝ) (Stage99KernelData.Cell157.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell157.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell157

theorem stage99_cell159 : (rectangle (99,159)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell159.interval.lo:ℝ) (Stage99KernelData.Cell159.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell159.mlo:ℝ) (Stage99KernelData.Cell159.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell159.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm

#print axioms stage99_cell159

end ForestUnimodality.IntermediateBridgeForestData
