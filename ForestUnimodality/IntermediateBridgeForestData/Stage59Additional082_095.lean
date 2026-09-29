import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell082.Conclusion
import ForestUnimodality.Stage59KernelData.Cell083.Conclusion
import ForestUnimodality.Stage59KernelData.Cell084.Conclusion
import ForestUnimodality.Stage59KernelData.Cell085.Conclusion
import ForestUnimodality.Stage59KernelData.Cell086.Conclusion
import ForestUnimodality.Stage59KernelData.Cell087.Conclusion
import ForestUnimodality.Stage59KernelData.Cell088.Conclusion
import ForestUnimodality.Stage59KernelData.Cell089.Conclusion
import ForestUnimodality.Stage59KernelData.Cell090.Conclusion
import ForestUnimodality.Stage59KernelData.Cell091.Conclusion
import ForestUnimodality.Stage59KernelData.Cell092.Conclusion
import ForestUnimodality.Stage59KernelData.Cell093.Conclusion
import ForestUnimodality.Stage59KernelData.Cell094.Conclusion
import ForestUnimodality.Stage59KernelData.Cell095.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell082 : (rectangle (59,82)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell082.interval.lo:ℝ) (Stage59KernelData.Cell082.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell082.mlo:ℝ) (Stage59KernelData.Cell082.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell082.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell082

theorem stage59_cell083 : (rectangle (59,83)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell083.interval.lo:ℝ) (Stage59KernelData.Cell083.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell083.mlo:ℝ) (Stage59KernelData.Cell083.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell083.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell083

theorem stage59_cell084 : (rectangle (59,84)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell084.interval.lo:ℝ) (Stage59KernelData.Cell084.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell084.mlo:ℝ) (Stage59KernelData.Cell084.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell084.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell084

theorem stage59_cell085 : (rectangle (59,85)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell085.interval.lo:ℝ) (Stage59KernelData.Cell085.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell085.mlo:ℝ) (Stage59KernelData.Cell085.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell085.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell085

theorem stage59_cell086 : (rectangle (59,86)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell086.interval.lo:ℝ) (Stage59KernelData.Cell086.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell086.mlo:ℝ) (Stage59KernelData.Cell086.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell086.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell086

theorem stage59_cell087 : (rectangle (59,87)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell087.interval.lo:ℝ) (Stage59KernelData.Cell087.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell087.mlo:ℝ) (Stage59KernelData.Cell087.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell087.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell087

theorem stage59_cell088 : (rectangle (59,88)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell088.interval.lo:ℝ) (Stage59KernelData.Cell088.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell088.mlo:ℝ) (Stage59KernelData.Cell088.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell088.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell088

theorem stage59_cell089 : (rectangle (59,89)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell089.interval.lo:ℝ) (Stage59KernelData.Cell089.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell089.mlo:ℝ) (Stage59KernelData.Cell089.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell089.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell089

theorem stage59_cell090 : (rectangle (59,90)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell090.interval.lo:ℝ) (Stage59KernelData.Cell090.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell090.mlo:ℝ) (Stage59KernelData.Cell090.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell090.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell090

theorem stage59_cell091 : (rectangle (59,91)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell091.interval.lo:ℝ) (Stage59KernelData.Cell091.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell091.mlo:ℝ) (Stage59KernelData.Cell091.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell091.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell091

theorem stage59_cell092 : (rectangle (59,92)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell092.interval.lo:ℝ) (Stage59KernelData.Cell092.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell092.mlo:ℝ) (Stage59KernelData.Cell092.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell092.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell092

theorem stage59_cell093 : (rectangle (59,93)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell093.interval.lo:ℝ) (Stage59KernelData.Cell093.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell093.mlo:ℝ) (Stage59KernelData.Cell093.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell093.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell093

theorem stage59_cell094 : (rectangle (59,94)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell094.interval.lo:ℝ) (Stage59KernelData.Cell094.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell094.mlo:ℝ) (Stage59KernelData.Cell094.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell094.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell094

theorem stage59_cell095 : (rectangle (59,95)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell095.interval.lo:ℝ) (Stage59KernelData.Cell095.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell095.mlo:ℝ) (Stage59KernelData.Cell095.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell095.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell095

end ForestUnimodality.IntermediateBridgeForestData
