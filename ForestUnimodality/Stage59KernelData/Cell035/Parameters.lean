import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell035
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (3345438260674269060092143821 / 12500000000000000000000000000)
  probabilityCap := (1687 / 3572)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 18), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (841 / 945)
def activityUpper : ℚ := (1687 / 1885)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (866439983350429293795969 / 200000000000000000000000)
  B := (-1064507060382294117983903 / 10000000000000000000000000)
  C := (-247583385746361732404619 / 625000000000000000000000)
  dδ := (1756290063355146757739789 / 10000000000000000000000000)
  dM := (0)
  wL := (344641214717 / 125000000000)
  wR := (3107175705659 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(4050067366270692303942269 / 500000000000000000000000), (598606400823016859824577 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (650557230431499089462477 / 50000000000000000000000) else if j = 1 then (592422521942008444284511 / 20000000000000000000000) else if j = 2 then (2170252448195126504515429 / 100000000000000000000000) else if j = 3 then (1892562876904312219039639 / 100000000000000000000000) else if j = 4 then (833724011762157424243469 / 50000000000000000000000) else if j = 5 then (1083512666241785105114559 / 50000000000000000000000) else if j = 6 then (461140067561290010189623 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (20646546771369356229112759 / 500000000000000000000000000000) else if j = 1 then (78798508299619382371108671 / 500000000000000000000000000000) else if j = 2 then (114461022281100946354713573 / 500000000000000000000000000000) else if j = 3 then (265628276366633197971964219 / 1000000000000000000000000000000) else if j = 4 then (265628276366633197971964219 / 1000000000000000000000000000000) else if j = 5 then (265628276366633197971964219 / 1000000000000000000000000000000) else if j = 6 then (265628276366633197971964219 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (841 / 1786)
  hi := (1687 / 3572)
  vmin := (794745 / 3189796)
  damping := (794745 / 3189796)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell035
