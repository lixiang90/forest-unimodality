import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage130KernelData.Cell011.Conclusion
import ForestUnimodality.Stage130KernelData.Cell012.Conclusion
import ForestUnimodality.Stage130KernelData.Cell013.Conclusion
import ForestUnimodality.Stage130KernelData.Cell014.Conclusion
import ForestUnimodality.Stage130KernelData.Cell015.Conclusion
import ForestUnimodality.Stage130KernelData.Cell016.Conclusion
import ForestUnimodality.Stage130KernelData.Cell017.Conclusion
import ForestUnimodality.Stage130KernelData.Cell018.Conclusion
import ForestUnimodality.Stage130KernelData.Cell023.Conclusion
import ForestUnimodality.Stage130KernelData.Cell024.Conclusion
import ForestUnimodality.Stage130KernelData.Cell025.Conclusion
import ForestUnimodality.Stage130KernelData.Cell026.Conclusion
import ForestUnimodality.Stage130KernelData.Cell027.Conclusion
import ForestUnimodality.Stage130KernelData.Cell028.Conclusion
import ForestUnimodality.Stage130KernelData.Cell029.Conclusion

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage130_cell011 : (rectangle (130,11)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell011.interval.lo:ℝ) (Stage130KernelData.Cell011.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell011.mlo:ℝ) (Stage130KernelData.Cell011.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell011.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell011

theorem stage130_cell012 : (rectangle (130,12)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell012.interval.lo:ℝ) (Stage130KernelData.Cell012.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell012.mlo:ℝ) (Stage130KernelData.Cell012.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell012.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell012

theorem stage130_cell013 : (rectangle (130,13)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell013.interval.lo:ℝ) (Stage130KernelData.Cell013.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell013.mlo:ℝ) (Stage130KernelData.Cell013.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell013.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell013

theorem stage130_cell014 : (rectangle (130,14)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell014.interval.lo:ℝ) (Stage130KernelData.Cell014.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell014.mlo:ℝ) (Stage130KernelData.Cell014.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell014.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell014

theorem stage130_cell015 : (rectangle (130,15)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell015.interval.lo:ℝ) (Stage130KernelData.Cell015.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell015.mlo:ℝ) (Stage130KernelData.Cell015.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell015.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell015

theorem stage130_cell016 : (rectangle (130,16)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell016.interval.lo:ℝ) (Stage130KernelData.Cell016.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell016.mlo:ℝ) (Stage130KernelData.Cell016.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell016.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell016

theorem stage130_cell017 : (rectangle (130,17)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell017.interval.lo:ℝ) (Stage130KernelData.Cell017.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell017.mlo:ℝ) (Stage130KernelData.Cell017.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell017.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell017

theorem stage130_cell018 : (rectangle (130,18)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell018.interval.lo:ℝ) (Stage130KernelData.Cell018.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell018.mlo:ℝ) (Stage130KernelData.Cell018.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell018.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell018

theorem stage130_cell023 : (rectangle (130,23)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell023.interval.lo:ℝ) (Stage130KernelData.Cell023.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell023.mlo:ℝ) (Stage130KernelData.Cell023.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell023.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell023

theorem stage130_cell024 : (rectangle (130,24)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell024.interval.lo:ℝ) (Stage130KernelData.Cell024.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell024.mlo:ℝ) (Stage130KernelData.Cell024.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell024.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell024

theorem stage130_cell025 : (rectangle (130,25)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell025.interval.lo:ℝ) (Stage130KernelData.Cell025.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell025.mlo:ℝ) (Stage130KernelData.Cell025.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell025.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell025

theorem stage130_cell026 : (rectangle (130,26)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell026.interval.lo:ℝ) (Stage130KernelData.Cell026.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell026.mlo:ℝ) (Stage130KernelData.Cell026.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell026.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell026

theorem stage130_cell027 : (rectangle (130,27)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell027.interval.lo:ℝ) (Stage130KernelData.Cell027.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell027.mlo:ℝ) (Stage130KernelData.Cell027.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell027.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell027

theorem stage130_cell028 : (rectangle (130,28)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell028.interval.lo:ℝ) (Stage130KernelData.Cell028.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell028.mlo:ℝ) (Stage130KernelData.Cell028.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell028.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell028

theorem stage130_cell029 : (rectangle (130,29)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤169 ∧
      z/(1+z)∈Set.Icc (Stage130KernelData.Cell029.interval.lo:ℝ) (Stage130KernelData.Cell029.interval.hi:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc (Stage130KernelData.Cell029.mlo:ℝ) (Stage130KernelData.Cell029.mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage130KernelData.Cell029.actual_no_weak_valley k hB hG (by omega) hN hz hk hq hrank hmean hm

#print axioms stage130_cell029

end ForestUnimodality.IntermediateBridgeForestData
