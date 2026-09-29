import ForestUnimodality.Stage59KernelData.Cell000.Conclusion
import ForestUnimodality.Stage59KernelData.Cell001.Conclusion
import ForestUnimodality.Stage59KernelData.Cell002.Conclusion
import ForestUnimodality.Stage59KernelData.Cell003.Conclusion
import ForestUnimodality.Stage59KernelData.Cell004.Conclusion
import ForestUnimodality.Stage59KernelData.Cell005.Conclusion
import ForestUnimodality.Stage59KernelData.Cell006.Conclusion
import ForestUnimodality.Stage59KernelData.Cell007.Conclusion
import ForestUnimodality.Stage59KernelData.Cell008.Conclusion
import ForestUnimodality.Stage59KernelData.Cell009.Conclusion
import ForestUnimodality.Stage59KernelData.Cell010.Conclusion
import ForestUnimodality.Stage59KernelData.Cell011.Conclusion
import ForestUnimodality.Stage59KernelData.Cell012.Conclusion
import ForestUnimodality.Stage59KernelData.Cell013.Conclusion
import ForestUnimodality.Stage59KernelData.Cell014.Conclusion
import ForestUnimodality.Stage59KernelData.Cell015.Conclusion
import ForestUnimodality.Stage59KernelData.Cell016.Conclusion
import ForestUnimodality.Stage59KernelData.Cell017.Conclusion
import ForestUnimodality.Stage59KernelData.Cell018.Conclusion
import ForestUnimodality.Stage59KernelData.Cell019.Conclusion
import ForestUnimodality.Stage59KernelData.Cell020.Conclusion
import ForestUnimodality.Stage59KernelData.Cell021.Conclusion
import ForestUnimodality.Stage59KernelData.Cell022.Conclusion
import ForestUnimodality.Stage59KernelData.Cell023.Conclusion
import ForestUnimodality.Stage59KernelData.Cell024.Conclusion
import ForestUnimodality.Stage59KernelData.Cell025.Conclusion
import ForestUnimodality.Stage59KernelData.Cell026.Conclusion
import ForestUnimodality.Stage59KernelData.Cell027.Conclusion
import ForestUnimodality.Stage59KernelData.Cell028.Conclusion
import ForestUnimodality.Stage59KernelData.Cell029.Conclusion
import ForestUnimodality.Stage59KernelData.Cell030.Conclusion
import ForestUnimodality.Stage59KernelData.Cell031.Conclusion
import ForestUnimodality.Stage59KernelData.Cell032.Conclusion
import ForestUnimodality.Stage59KernelData.Cell033.Conclusion
import ForestUnimodality.Stage59KernelData.Cell034.Conclusion
import ForestUnimodality.Stage59KernelData.Cell035.Conclusion
import ForestUnimodality.Stage59KernelData.Cell036.Conclusion
import ForestUnimodality.Stage59KernelData.Cell037.Conclusion
import ForestUnimodality.Stage59KernelData.Cell038.Conclusion
import ForestUnimodality.Stage59KernelData.Cell039.Conclusion
import ForestUnimodality.Stage59KernelData.Cell040.Conclusion
import ForestUnimodality.Stage59KernelData.Cell041.Conclusion
import ForestUnimodality.Stage59KernelData.Cell042.Conclusion
import ForestUnimodality.Stage59KernelData.Cell043.Conclusion
import ForestUnimodality.Stage59KernelData.Cell044.Conclusion
import ForestUnimodality.Stage59KernelData.Cell045.Conclusion
import ForestUnimodality.Stage59KernelData.Cell046.Conclusion

/-! The first forty-seven actual count rectangles, indices 0..46.
This library does not claim full stage coverage. -/
namespace ForestUnimodality.Stage59InitialRectangles

structure Rectangle where
  qa : ℚ
  qb : ℚ
  mlo : ℚ
  mhi : ℚ

def rectangle : Fin 47 → Rectangle := ![
  ⟨Stage59KernelData.Cell000.interval.lo, Stage59KernelData.Cell000.interval.hi, Stage59KernelData.Cell000.mlo, Stage59KernelData.Cell000.mhi⟩,
  ⟨Stage59KernelData.Cell001.interval.lo, Stage59KernelData.Cell001.interval.hi, Stage59KernelData.Cell001.mlo, Stage59KernelData.Cell001.mhi⟩,
  ⟨Stage59KernelData.Cell002.interval.lo, Stage59KernelData.Cell002.interval.hi, Stage59KernelData.Cell002.mlo, Stage59KernelData.Cell002.mhi⟩,
  ⟨Stage59KernelData.Cell003.interval.lo, Stage59KernelData.Cell003.interval.hi, Stage59KernelData.Cell003.mlo, Stage59KernelData.Cell003.mhi⟩,
  ⟨Stage59KernelData.Cell004.interval.lo, Stage59KernelData.Cell004.interval.hi, Stage59KernelData.Cell004.mlo, Stage59KernelData.Cell004.mhi⟩,
  ⟨Stage59KernelData.Cell005.interval.lo, Stage59KernelData.Cell005.interval.hi, Stage59KernelData.Cell005.mlo, Stage59KernelData.Cell005.mhi⟩,
  ⟨Stage59KernelData.Cell006.interval.lo, Stage59KernelData.Cell006.interval.hi, Stage59KernelData.Cell006.mlo, Stage59KernelData.Cell006.mhi⟩,
  ⟨Stage59KernelData.Cell007.interval.lo, Stage59KernelData.Cell007.interval.hi, Stage59KernelData.Cell007.mlo, Stage59KernelData.Cell007.mhi⟩,
  ⟨Stage59KernelData.Cell008.interval.lo, Stage59KernelData.Cell008.interval.hi, Stage59KernelData.Cell008.mlo, Stage59KernelData.Cell008.mhi⟩,
  ⟨Stage59KernelData.Cell009.interval.lo, Stage59KernelData.Cell009.interval.hi, Stage59KernelData.Cell009.mlo, Stage59KernelData.Cell009.mhi⟩,
  ⟨Stage59KernelData.Cell010.interval.lo, Stage59KernelData.Cell010.interval.hi, Stage59KernelData.Cell010.mlo, Stage59KernelData.Cell010.mhi⟩,
  ⟨Stage59KernelData.Cell011.interval.lo, Stage59KernelData.Cell011.interval.hi, Stage59KernelData.Cell011.mlo, Stage59KernelData.Cell011.mhi⟩,
  ⟨Stage59KernelData.Cell012.interval.lo, Stage59KernelData.Cell012.interval.hi, Stage59KernelData.Cell012.mlo, Stage59KernelData.Cell012.mhi⟩,
  ⟨Stage59KernelData.Cell013.interval.lo, Stage59KernelData.Cell013.interval.hi, Stage59KernelData.Cell013.mlo, Stage59KernelData.Cell013.mhi⟩,
  ⟨Stage59KernelData.Cell014.interval.lo, Stage59KernelData.Cell014.interval.hi, Stage59KernelData.Cell014.mlo, Stage59KernelData.Cell014.mhi⟩,
  ⟨Stage59KernelData.Cell015.interval.lo, Stage59KernelData.Cell015.interval.hi, Stage59KernelData.Cell015.mlo, Stage59KernelData.Cell015.mhi⟩,
  ⟨Stage59KernelData.Cell016.interval.lo, Stage59KernelData.Cell016.interval.hi, Stage59KernelData.Cell016.mlo, Stage59KernelData.Cell016.mhi⟩,
  ⟨Stage59KernelData.Cell017.interval.lo, Stage59KernelData.Cell017.interval.hi, Stage59KernelData.Cell017.mlo, Stage59KernelData.Cell017.mhi⟩,
  ⟨Stage59KernelData.Cell018.interval.lo, Stage59KernelData.Cell018.interval.hi, Stage59KernelData.Cell018.mlo, Stage59KernelData.Cell018.mhi⟩,
  ⟨Stage59KernelData.Cell019.interval.lo, Stage59KernelData.Cell019.interval.hi, Stage59KernelData.Cell019.mlo, Stage59KernelData.Cell019.mhi⟩,
  ⟨Stage59KernelData.Cell020.interval.lo, Stage59KernelData.Cell020.interval.hi, Stage59KernelData.Cell020.mlo, Stage59KernelData.Cell020.mhi⟩,
  ⟨Stage59KernelData.Cell021.interval.lo, Stage59KernelData.Cell021.interval.hi, Stage59KernelData.Cell021.mlo, Stage59KernelData.Cell021.mhi⟩,
  ⟨Stage59KernelData.Cell022.interval.lo, Stage59KernelData.Cell022.interval.hi, Stage59KernelData.Cell022.mlo, Stage59KernelData.Cell022.mhi⟩,
  ⟨Stage59KernelData.Cell023.interval.lo, Stage59KernelData.Cell023.interval.hi, Stage59KernelData.Cell023.mlo, Stage59KernelData.Cell023.mhi⟩,
  ⟨Stage59KernelData.Cell024.interval.lo, Stage59KernelData.Cell024.interval.hi, Stage59KernelData.Cell024.mlo, Stage59KernelData.Cell024.mhi⟩,
  ⟨Stage59KernelData.Cell025.interval.lo, Stage59KernelData.Cell025.interval.hi, Stage59KernelData.Cell025.mlo, Stage59KernelData.Cell025.mhi⟩,
  ⟨Stage59KernelData.Cell026.interval.lo, Stage59KernelData.Cell026.interval.hi, Stage59KernelData.Cell026.mlo, Stage59KernelData.Cell026.mhi⟩,
  ⟨Stage59KernelData.Cell027.interval.lo, Stage59KernelData.Cell027.interval.hi, Stage59KernelData.Cell027.mlo, Stage59KernelData.Cell027.mhi⟩,
  ⟨Stage59KernelData.Cell028.interval.lo, Stage59KernelData.Cell028.interval.hi, Stage59KernelData.Cell028.mlo, Stage59KernelData.Cell028.mhi⟩,
  ⟨Stage59KernelData.Cell029.interval.lo, Stage59KernelData.Cell029.interval.hi, Stage59KernelData.Cell029.mlo, Stage59KernelData.Cell029.mhi⟩,
  ⟨Stage59KernelData.Cell030.interval.lo, Stage59KernelData.Cell030.interval.hi, Stage59KernelData.Cell030.mlo, Stage59KernelData.Cell030.mhi⟩,
  ⟨Stage59KernelData.Cell031.interval.lo, Stage59KernelData.Cell031.interval.hi, Stage59KernelData.Cell031.mlo, Stage59KernelData.Cell031.mhi⟩,
  ⟨Stage59KernelData.Cell032.interval.lo, Stage59KernelData.Cell032.interval.hi, Stage59KernelData.Cell032.mlo, Stage59KernelData.Cell032.mhi⟩,
  ⟨Stage59KernelData.Cell033.interval.lo, Stage59KernelData.Cell033.interval.hi, Stage59KernelData.Cell033.mlo, Stage59KernelData.Cell033.mhi⟩,
  ⟨Stage59KernelData.Cell034.interval.lo, Stage59KernelData.Cell034.interval.hi, Stage59KernelData.Cell034.mlo, Stage59KernelData.Cell034.mhi⟩,
  ⟨Stage59KernelData.Cell035.interval.lo, Stage59KernelData.Cell035.interval.hi, Stage59KernelData.Cell035.mlo, Stage59KernelData.Cell035.mhi⟩,
  ⟨Stage59KernelData.Cell036.interval.lo, Stage59KernelData.Cell036.interval.hi, Stage59KernelData.Cell036.mlo, Stage59KernelData.Cell036.mhi⟩,
  ⟨Stage59KernelData.Cell037.interval.lo, Stage59KernelData.Cell037.interval.hi, Stage59KernelData.Cell037.mlo, Stage59KernelData.Cell037.mhi⟩,
  ⟨Stage59KernelData.Cell038.interval.lo, Stage59KernelData.Cell038.interval.hi, Stage59KernelData.Cell038.mlo, Stage59KernelData.Cell038.mhi⟩,
  ⟨Stage59KernelData.Cell039.interval.lo, Stage59KernelData.Cell039.interval.hi, Stage59KernelData.Cell039.mlo, Stage59KernelData.Cell039.mhi⟩,
  ⟨Stage59KernelData.Cell040.interval.lo, Stage59KernelData.Cell040.interval.hi, Stage59KernelData.Cell040.mlo, Stage59KernelData.Cell040.mhi⟩,
  ⟨Stage59KernelData.Cell041.interval.lo, Stage59KernelData.Cell041.interval.hi, Stage59KernelData.Cell041.mlo, Stage59KernelData.Cell041.mhi⟩,
  ⟨Stage59KernelData.Cell042.interval.lo, Stage59KernelData.Cell042.interval.hi, Stage59KernelData.Cell042.mlo, Stage59KernelData.Cell042.mhi⟩,
  ⟨Stage59KernelData.Cell043.interval.lo, Stage59KernelData.Cell043.interval.hi, Stage59KernelData.Cell043.mlo, Stage59KernelData.Cell043.mhi⟩,
  ⟨Stage59KernelData.Cell044.interval.lo, Stage59KernelData.Cell044.interval.hi, Stage59KernelData.Cell044.mlo, Stage59KernelData.Cell044.mhi⟩,
  ⟨Stage59KernelData.Cell045.interval.lo, Stage59KernelData.Cell045.interval.hi, Stage59KernelData.Cell045.mlo, Stage59KernelData.Cell045.mhi⟩,
  ⟨Stage59KernelData.Cell046.interval.lo, Stage59KernelData.Cell046.interval.hi, Stage59KernelData.Cell046.mlo, Stage59KernelData.Cell046.mhi⟩]

variable {V : Type*} [DecidableEq V]
theorem no_weak_valley (i : Fin 47) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 59 ≤ S.card) (hN : S.card ≤ 79) (hz : 0 < z)
    (hq : z/(1+z) ∈ Set.Icc ((rectangle i).qa : ℝ) ((rectangle i).qb : ℝ))
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z) (hmean : hardCoreMean G S z = k)
    (hm : hardCoreAvailableMean G S B z ∈ Set.Icc ((rectangle i).mlo : ℝ) ((rectangle i).mhi : ℝ)) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k-1) ∧
      countIndependent G S k ≤ countIndependent G S (k+1)) := by
  fin_cases i
  · intro h
    exact (not_lt_of_ge h.1)
      (Stage59KernelData.Cell000.actual_left_coefficient_lt k hB hG hn hN hz hq hrank hmean hm)
  · exact Stage59KernelData.Cell001.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell002.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell003.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell004.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell005.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell006.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell007.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell008.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell009.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell010.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell011.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell012.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell013.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell014.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell015.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell016.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell017.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell018.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell019.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell020.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell021.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell022.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell023.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell024.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell025.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell026.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell027.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell028.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell029.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell030.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell031.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell032.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell033.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell034.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell035.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell036.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell037.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell038.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell039.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell040.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell041.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell042.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell043.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell044.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell045.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm
  · exact Stage59KernelData.Cell046.actual_no_weak_valley k hB hG hn hN hz hq hrank hmean hm

#print axioms no_weak_valley
end ForestUnimodality.Stage59InitialRectangles
