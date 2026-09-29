import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59KernelData.Cell066.Conclusion
import ForestUnimodality.Stage59KernelData.Cell067.Conclusion
import ForestUnimodality.Stage59KernelData.Cell068.Conclusion
import ForestUnimodality.Stage59KernelData.Cell069.Conclusion
import ForestUnimodality.Stage59KernelData.Cell070.Conclusion
import ForestUnimodality.Stage59KernelData.Cell071.Conclusion
import ForestUnimodality.Stage59KernelData.Cell072.Conclusion
import ForestUnimodality.Stage59KernelData.Cell073.Conclusion
import ForestUnimodality.Stage59KernelData.Cell074.Conclusion
import ForestUnimodality.Stage59KernelData.Cell075.Conclusion
import ForestUnimodality.Stage59KernelData.Cell076.Conclusion
import ForestUnimodality.Stage59KernelData.Cell077.Conclusion
import ForestUnimodality.Stage59KernelData.Cell078.Conclusion
import ForestUnimodality.Stage59KernelData.Cell079.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell066 : (rectangle (59,66)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell066.interval.lo:ℝ) (Stage59KernelData.Cell066.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell066.mlo:ℝ) (Stage59KernelData.Cell066.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell066.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell066

theorem stage59_cell067 : (rectangle (59,67)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell067.interval.lo:ℝ) (Stage59KernelData.Cell067.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell067.mlo:ℝ) (Stage59KernelData.Cell067.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell067.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell067

theorem stage59_cell068 : (rectangle (59,68)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell068.interval.lo:ℝ) (Stage59KernelData.Cell068.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell068.mlo:ℝ) (Stage59KernelData.Cell068.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell068.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell068

theorem stage59_cell069 : (rectangle (59,69)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell069.interval.lo:ℝ) (Stage59KernelData.Cell069.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell069.mlo:ℝ) (Stage59KernelData.Cell069.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell069.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell069

theorem stage59_cell070 : (rectangle (59,70)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell070.interval.lo:ℝ) (Stage59KernelData.Cell070.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell070.mlo:ℝ) (Stage59KernelData.Cell070.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell070.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell070

theorem stage59_cell071 : (rectangle (59,71)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell071.interval.lo:ℝ) (Stage59KernelData.Cell071.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell071.mlo:ℝ) (Stage59KernelData.Cell071.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell071.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell071

theorem stage59_cell072 : (rectangle (59,72)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell072.interval.lo:ℝ) (Stage59KernelData.Cell072.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell072.mlo:ℝ) (Stage59KernelData.Cell072.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell072.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell072

theorem stage59_cell073 : (rectangle (59,73)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell073.interval.lo:ℝ) (Stage59KernelData.Cell073.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell073.mlo:ℝ) (Stage59KernelData.Cell073.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell073.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell073

theorem stage59_cell074 : (rectangle (59,74)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell074.interval.lo:ℝ) (Stage59KernelData.Cell074.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell074.mlo:ℝ) (Stage59KernelData.Cell074.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell074.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell074

theorem stage59_cell075 : (rectangle (59,75)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell075.interval.lo:ℝ) (Stage59KernelData.Cell075.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell075.mlo:ℝ) (Stage59KernelData.Cell075.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell075.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell075

theorem stage59_cell076 : (rectangle (59,76)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell076.interval.lo:ℝ) (Stage59KernelData.Cell076.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell076.mlo:ℝ) (Stage59KernelData.Cell076.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell076.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell076

theorem stage59_cell077 : (rectangle (59,77)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell077.interval.lo:ℝ) (Stage59KernelData.Cell077.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell077.mlo:ℝ) (Stage59KernelData.Cell077.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell077.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell077

theorem stage59_cell078 : (rectangle (59,78)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell078.interval.lo:ℝ) (Stage59KernelData.Cell078.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell078.mlo:ℝ) (Stage59KernelData.Cell078.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell078.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell078

theorem stage59_cell079 : (rectangle (59,79)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc (Stage59KernelData.Cell079.interval.lo:ℝ) (Stage59KernelData.Cell079.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage59KernelData.Cell079.mlo:ℝ) (Stage59KernelData.Cell079.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59KernelData.Cell079.actual_no_weak_valley k hB hG (by omega) hN hz hq hrank hmean hm

#print axioms stage59_cell079

end ForestUnimodality.IntermediateBridgeForestData
