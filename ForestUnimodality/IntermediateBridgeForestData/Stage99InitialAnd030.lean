import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage99KernelData.Cell000.Conclusion
import ForestUnimodality.Stage99KernelData.Cell001.Conclusion
import ForestUnimodality.Stage99KernelData.Cell002.Conclusion
import ForestUnimodality.Stage99KernelData.Cell003.Conclusion
import ForestUnimodality.Stage99KernelData.Cell004.Conclusion
import ForestUnimodality.Stage99KernelData.Cell005.Conclusion
import ForestUnimodality.Stage99KernelData.Cell006.Conclusion
import ForestUnimodality.Stage99KernelData.Cell007.Conclusion
import ForestUnimodality.Stage99KernelData.Cell008.Conclusion
import ForestUnimodality.Stage99KernelData.Cell009.Conclusion
import ForestUnimodality.Stage99KernelData.Cell010.Conclusion
import ForestUnimodality.Stage99KernelData.Cell030.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage99_cell000 : (rectangle (99,0)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell000.interval.lo:ℝ) (Stage99KernelData.Cell000.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell000.mlo:ℝ) (Stage99KernelData.Cell000.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell000.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell000

theorem stage99_cell001 : (rectangle (99,1)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell001.interval.lo:ℝ) (Stage99KernelData.Cell001.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell001.mlo:ℝ) (Stage99KernelData.Cell001.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell001.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell001

theorem stage99_cell002 : (rectangle (99,2)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell002.interval.lo:ℝ) (Stage99KernelData.Cell002.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell002.mlo:ℝ) (Stage99KernelData.Cell002.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell002.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell002

theorem stage99_cell003 : (rectangle (99,3)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell003.interval.lo:ℝ) (Stage99KernelData.Cell003.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell003.mlo:ℝ) (Stage99KernelData.Cell003.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell003.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell003

theorem stage99_cell004 : (rectangle (99,4)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell004.interval.lo:ℝ) (Stage99KernelData.Cell004.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell004.mlo:ℝ) (Stage99KernelData.Cell004.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell004.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell004

theorem stage99_cell005 : (rectangle (99,5)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell005.interval.lo:ℝ) (Stage99KernelData.Cell005.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell005.mlo:ℝ) (Stage99KernelData.Cell005.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell005.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell005

theorem stage99_cell006 : (rectangle (99,6)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell006.interval.lo:ℝ) (Stage99KernelData.Cell006.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell006.mlo:ℝ) (Stage99KernelData.Cell006.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell006.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell006

theorem stage99_cell007 : (rectangle (99,7)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell007.interval.lo:ℝ) (Stage99KernelData.Cell007.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell007.mlo:ℝ) (Stage99KernelData.Cell007.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell007.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell007

theorem stage99_cell008 : (rectangle (99,8)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell008.interval.lo:ℝ) (Stage99KernelData.Cell008.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell008.mlo:ℝ) (Stage99KernelData.Cell008.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell008.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell008

theorem stage99_cell009 : (rectangle (99,9)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell009.interval.lo:ℝ) (Stage99KernelData.Cell009.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell009.mlo:ℝ) (Stage99KernelData.Cell009.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell009.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell009

theorem stage99_cell010 : (rectangle (99,10)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell010.interval.lo:ℝ) (Stage99KernelData.Cell010.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell010.mlo:ℝ) (Stage99KernelData.Cell010.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell010.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell010

theorem stage99_cell030 : (rectangle (99,30)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤129 ∧
      z/(1+z)∈Set.Icc (Stage99KernelData.Cell030.interval.lo:ℝ) (Stage99KernelData.Cell030.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage99KernelData.Cell030.mlo:ℝ) (Stage99KernelData.Cell030.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage99KernelData.Cell030.actual_no_weak_valley k hB hG (by omega) (by omega) hN hz hk hq hrank hmean hm
#print axioms stage99_cell030

end ForestUnimodality.IntermediateBridgeForestData
