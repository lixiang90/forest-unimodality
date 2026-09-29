import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell054.Conclusion
import ForestUnimodality.Stage59KernelData.Cell055.Conclusion
import ForestUnimodality.Stage59KernelData.Cell056.Conclusion
import ForestUnimodality.Stage59KernelData.Cell057.Conclusion
import ForestUnimodality.Stage59KernelData.Cell058.Conclusion
import ForestUnimodality.Stage59KernelData.Cell059.Conclusion
import ForestUnimodality.Stage59KernelData.Cell060.Conclusion
import ForestUnimodality.Stage59KernelData.Cell061.Conclusion
import ForestUnimodality.Stage59KernelData.Cell062.Conclusion
import ForestUnimodality.Stage59KernelData.Cell063.Conclusion
import ForestUnimodality.Stage59KernelData.Cell064.Conclusion
import ForestUnimodality.Stage59KernelData.Cell065.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell054 : (rectangle (59,54)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell054.interval.lo:ℝ) (Stage59KernelData.Cell054.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell054.mlo:ℝ) (Stage59KernelData.Cell054.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell054.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell054

theorem stage59_cell055 : (rectangle (59,55)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell055.interval.lo:ℝ) (Stage59KernelData.Cell055.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell055.mlo:ℝ) (Stage59KernelData.Cell055.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell055.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell055

theorem stage59_cell056 : (rectangle (59,56)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell056.interval.lo:ℝ) (Stage59KernelData.Cell056.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell056.mlo:ℝ) (Stage59KernelData.Cell056.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell056.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell056

theorem stage59_cell057 : (rectangle (59,57)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell057.interval.lo:ℝ) (Stage59KernelData.Cell057.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell057.mlo:ℝ) (Stage59KernelData.Cell057.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell057.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell057

theorem stage59_cell058 : (rectangle (59,58)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell058.interval.lo:ℝ) (Stage59KernelData.Cell058.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell058.mlo:ℝ) (Stage59KernelData.Cell058.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell058.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell058

theorem stage59_cell059 : (rectangle (59,59)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell059.interval.lo:ℝ) (Stage59KernelData.Cell059.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell059.mlo:ℝ) (Stage59KernelData.Cell059.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell059.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell059

theorem stage59_cell060 : (rectangle (59,60)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell060.interval.lo:ℝ) (Stage59KernelData.Cell060.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell060.mlo:ℝ) (Stage59KernelData.Cell060.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell060.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell060

theorem stage59_cell061 : (rectangle (59,61)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell061.interval.lo:ℝ) (Stage59KernelData.Cell061.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell061.mlo:ℝ) (Stage59KernelData.Cell061.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell061.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell061

theorem stage59_cell062 : (rectangle (59,62)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell062.interval.lo:ℝ) (Stage59KernelData.Cell062.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell062.mlo:ℝ) (Stage59KernelData.Cell062.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell062.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell062

theorem stage59_cell063 : (rectangle (59,63)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell063.interval.lo:ℝ) (Stage59KernelData.Cell063.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell063.mlo:ℝ) (Stage59KernelData.Cell063.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell063.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell063

theorem stage59_cell064 : (rectangle (59,64)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell064.interval.lo:ℝ) (Stage59KernelData.Cell064.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell064.mlo:ℝ) (Stage59KernelData.Cell064.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell064.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell064

theorem stage59_cell065 : (rectangle (59,65)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell065.interval.lo:ℝ) (Stage59KernelData.Cell065.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell065.mlo:ℝ) (Stage59KernelData.Cell065.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell065.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell065

end ForestUnimodality.IntermediateBridgeForestData
