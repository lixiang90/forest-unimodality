import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell108.Conclusion
import ForestUnimodality.Stage59KernelData.Cell109.Conclusion
import ForestUnimodality.Stage59KernelData.Cell110.Conclusion
import ForestUnimodality.Stage59KernelData.Cell111.Conclusion
import ForestUnimodality.Stage59KernelData.Cell112.Conclusion
import ForestUnimodality.Stage59KernelData.Cell113.Conclusion
import ForestUnimodality.Stage59KernelData.Cell114.Conclusion
import ForestUnimodality.Stage59KernelData.Cell115.Conclusion
import ForestUnimodality.Stage59KernelData.Cell116.Conclusion
import ForestUnimodality.Stage59KernelData.Cell117.Conclusion
import ForestUnimodality.Stage59KernelData.Cell118.Conclusion
import ForestUnimodality.Stage59KernelData.Cell119.Conclusion
import ForestUnimodality.Stage59KernelData.Cell120.Conclusion
import ForestUnimodality.Stage59KernelData.Cell121.Conclusion
import ForestUnimodality.Stage59KernelData.Cell122.Conclusion
import ForestUnimodality.Stage59KernelData.Cell202.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell108 : (rectangle (59,108)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell108.interval.lo:ℝ) (Stage59KernelData.Cell108.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell108.mlo:ℝ) (Stage59KernelData.Cell108.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell108.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell108

theorem stage59_cell109 : (rectangle (59,109)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell109.interval.lo:ℝ) (Stage59KernelData.Cell109.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell109.mlo:ℝ) (Stage59KernelData.Cell109.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell109.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell109

theorem stage59_cell110 : (rectangle (59,110)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell110.interval.lo:ℝ) (Stage59KernelData.Cell110.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell110.mlo:ℝ) (Stage59KernelData.Cell110.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell110.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell110

theorem stage59_cell111 : (rectangle (59,111)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell111.interval.lo:ℝ) (Stage59KernelData.Cell111.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell111.mlo:ℝ) (Stage59KernelData.Cell111.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell111.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell111

theorem stage59_cell112 : (rectangle (59,112)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell112.interval.lo:ℝ) (Stage59KernelData.Cell112.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell112.mlo:ℝ) (Stage59KernelData.Cell112.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell112.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell112

theorem stage59_cell113 : (rectangle (59,113)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell113.interval.lo:ℝ) (Stage59KernelData.Cell113.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell113.mlo:ℝ) (Stage59KernelData.Cell113.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell113.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell113

theorem stage59_cell114 : (rectangle (59,114)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell114.interval.lo:ℝ) (Stage59KernelData.Cell114.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell114.mlo:ℝ) (Stage59KernelData.Cell114.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell114.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell114

theorem stage59_cell115 : (rectangle (59,115)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell115.interval.lo:ℝ) (Stage59KernelData.Cell115.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell115.mlo:ℝ) (Stage59KernelData.Cell115.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell115.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell115

theorem stage59_cell116 : (rectangle (59,116)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell116.interval.lo:ℝ) (Stage59KernelData.Cell116.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell116.mlo:ℝ) (Stage59KernelData.Cell116.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell116.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell116

theorem stage59_cell117 : (rectangle (59,117)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell117.interval.lo:ℝ) (Stage59KernelData.Cell117.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell117.mlo:ℝ) (Stage59KernelData.Cell117.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell117.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell117

theorem stage59_cell118 : (rectangle (59,118)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell118.interval.lo:ℝ) (Stage59KernelData.Cell118.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell118.mlo:ℝ) (Stage59KernelData.Cell118.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell118.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell118

theorem stage59_cell119 : (rectangle (59,119)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell119.interval.lo:ℝ) (Stage59KernelData.Cell119.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell119.mlo:ℝ) (Stage59KernelData.Cell119.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell119.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell119

theorem stage59_cell120 : (rectangle (59,120)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell120.interval.lo:ℝ) (Stage59KernelData.Cell120.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell120.mlo:ℝ) (Stage59KernelData.Cell120.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell120.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell120

theorem stage59_cell121 : (rectangle (59,121)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell121.interval.lo:ℝ) (Stage59KernelData.Cell121.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell121.mlo:ℝ) (Stage59KernelData.Cell121.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell121.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell121

theorem stage59_cell122 : (rectangle (59,122)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell122.interval.lo:ℝ) (Stage59KernelData.Cell122.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell122.mlo:ℝ) (Stage59KernelData.Cell122.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell122.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell122

theorem stage59_cell202 : (rectangle (59,202)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell202.interval.lo:ℝ) (Stage59KernelData.Cell202.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell202.mlo:ℝ) (Stage59KernelData.Cell202.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell202.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hhalf hm

#print axioms stage59_cell202

end ForestUnimodality.IntermediateBridgeForestData
