import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell037
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (134077544585578531749777768827 / 500000000000000000000000000000)
  probabilityCap := (9 / 19)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 18), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1687 / 1885)
def activityUpper : ℚ := (9 / 10)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (3947678111937774543150681 / 1000000000000000000000000)
  B := (-1968547496018784315197081 / 20000000000000000000000000)
  C := (-3048277911662380379453907 / 10000000000000000000000000)
  dδ := (1639173966056908515742663 / 10000000000000000000000000)
  dM := (0)
  wL := (6488331598299 / 2500000000000)
  wR := (35116684017 / 25000000000)
  wC := (1 / 10000000000000)
  price := ![(3326904334072224855844979 / 500000000000000000000000), (2377103483228394154025409 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1507182778116454535677349 / 100000000000000000000000) else if j = 1 then (2764096026514804549378823 / 100000000000000000000000) else if j = 2 then (2025864378588450875895433 / 100000000000000000000000) else if j = 3 then (1547399867519354543787813 / 100000000000000000000000) else if j = 4 then (1427990566738276889680037 / 100000000000000000000000) else if j = 5 then (171931625733794746224703 / 10000000000000000000000) else if j = 6 then (1603185949866761106363811 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (20780690946516002035234203 / 500000000000000000000000000000) else if j = 1 then (19606180708906427583052479 / 125000000000000000000000000000) else if j = 2 then (28320038801753728731075803 / 125000000000000000000000000000) else if j = 3 then (6535393569635475861017493 / 25000000000000000000000000000) else if j = 4 then (6535393569635475861017493 / 25000000000000000000000000000) else if j = 5 then (6535393569635475861017493 / 25000000000000000000000000000) else if j = 6 then (6535393569635475861017493 / 25000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1687 / 3572)
  hi := (9 / 19)
  vmin := (3179995 / 12759184)
  damping := (3179995 / 12759184)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell037
