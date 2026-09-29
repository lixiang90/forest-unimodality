import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell081
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (276487894771556723313577579743 / 1000000000000000000000000000000)
  probabilityCap := (131 / 264)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (49 / 50)
def activityUpper : ℚ := (131 / 133)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3081534711902053442656779 / 1000000000000000000000000)
  B := (-3969473028675087750150041 / 50000000000000000000000000)
  C := (4491770280905788177705507 / 1000000000000000000000000000)
  dδ := (1264709531715931256634633 / 10000000000000000000000000)
  dM := (0)
  wL := (354233836587 / 250000000000)
  wR := (3532766616537 / 2500000000000)
  wC := (2924895017593 / 10000000000000)
  price := ![(6692502154745162634696953 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2241874374408645209655333 / 100000000000000000000000) else if j = 0 then (1753009979338738233423101 / 100000000000000000000000) else if j = 1 then (553809856490816265761623 / 25000000000000000000000) else if j = 2 then (59172091522095926485747 / 3125000000000000000000) else if j = 3 then (1326170275897936612352623 / 100000000000000000000000) else if j = 4 then (417072222665823755249903 / 25000000000000000000000) else if j = 5 then (9673586971524887445639251 / 1000000000000000000000000) else if j = 6 then (70815382418188779212187 / 5000000000000000000000) else if j = 7 then (599120158051855589143031 / 62500000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6484356179062903670554963 / 250000000000000000000000000000) else if j = 0 then (23633253343765428492153549 / 500000000000000000000000000000) else if j = 1 then (86118843237052330970323717 / 1000000000000000000000000000000) else if j = 2 then (17585676145267829834839689 / 125000000000000000000000000000) else if j = 3 then (1485466091244852655117573 / 8000000000000000000000000000) else if j = 4 then (48942204323806021400902861 / 250000000000000000000000000000) else if j = 5 then (48942204323806021400902861 / 250000000000000000000000000000) else if j = 6 then (48942204323806021400902861 / 250000000000000000000000000000) else if j = 7 then (167471727150416815667268117 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (131 / 264)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell081
