import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell041
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (134591196186980133748413716259 / 500000000000000000000000000000)
  probabilityCap := (869 / 1824)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1733 / 1915)
def activityUpper : ℚ := (869 / 955)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (27)
  A := (-987172238454695413267359 / 500000000000000000000000)
  B := (2547368647183284595669761 / 10000000000000000000000000)
  C := (-2512641176882103311029937 / 10000000000000000000000000)
  dδ := (1440472503165583506579139 / 10000000000000000000000000)
  dM := (2861717943337243122425839 / 500000000000000000000000000)
  wL := (3149602264617 / 1250000000000)
  wR := (740159094153 / 500000000000)
  wC := (1 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (477854811230595899473883 / 25000000000000000000000) else if j = 0 then (341562746839393005515717 / 25000000000000000000000) else if j = 1 then (3004223898610344178905507 / 100000000000000000000000) else if j = 2 then (1241411406938392580912023 / 50000000000000000000000) else if j = 3 then (63284424564827066461703 / 2500000000000000000000) else if j = 4 then (771712498262582169417101 / 25000000000000000000000) else if j = 5 then (1269416132518811757279309 / 25000000000000000000000) else if j = 6 then (7686140986584892687005777 / 100000000000000000000000) else if j = 7 then (9088886477553893428193987 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (10498117528945889707357339 / 250000000000000000000000000000) else if j = 0 then (42320841987693197180804911 / 500000000000000000000000000000) else if j = 1 then (155030318750467983535361297 / 1000000000000000000000000000000) else if j = 2 then (55371156711365362934163133 / 250000000000000000000000000000) else if j = 3 then (31595673094683453201234761 / 125000000000000000000000000000) else if j = 4 then (31595673094683453201234761 / 125000000000000000000000000000) else if j = 5 then (31595673094683453201234761 / 125000000000000000000000000000) else if j = 6 then (31595673094683453201234761 / 125000000000000000000000000000) else if j = 7 then (31595673094683453201234761 / 125000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1733 / 3648)
  hi := (869 / 1824)
  vmin := (3318695 / 13307904)
  damping := (3318695 / 13307904)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell041
