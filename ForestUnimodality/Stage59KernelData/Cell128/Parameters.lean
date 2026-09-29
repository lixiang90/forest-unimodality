import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell128
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (28399692098272751141556309037 / 100000000000000000000000000000)
  probabilityCap := (7339 / 14214)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (10996 / 10325)
def activityUpper : ℚ := (7339 / 6875)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (-237092538735833966654809 / 2000000000000000000000000)
  B := (621947672644195467817063 / 5000000000000000000000000)
  C := (4203378974951060831344307 / 50000000000000000000000000)
  dδ := (1287635967218002941425681 / 10000000000000000000000000)
  dM := (3491461031717120640227581 / 1000000000000000000000000000)
  wL := (179914726977 / 100000000000)
  wR := (2751065912787 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(2383714008525550376305091 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (499911328603741367260227 / 20000000000000000000000) else if j = 0 then (3059913501497016241614801 / 100000000000000000000000) else if j = 1 then (4754784300175609246252861 / 100000000000000000000000) else if j = 2 then (2896872695297395949864949 / 50000000000000000000000) else if j = 3 then (1840292254285100170818623 / 100000000000000000000000) else if j = 4 then (216820877459335257242401 / 10000000000000000000000) else if j = 5 then (1361749019277168493147201 / 50000000000000000000000) else if j = 6 then (3480844905213987061642911 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (82858793425648023922091 / 3125000000000000000000000000) else if j = 0 then (44179833940295796916927993 / 1000000000000000000000000000000) else if j = 1 then (593033466611845464865423 / 7812500000000000000000000000) else if j = 2 then (3703597295686458255847557 / 31250000000000000000000000000) else if j = 3 then (72164383878343579586619519 / 500000000000000000000000000000) else if j = 4 then (72164383878343579586619519 / 500000000000000000000000000000) else if j = 5 then (72164383878343579586619519 / 500000000000000000000000000000) else if j = 6 then (72164383878343579586619519 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (10996 / 21321)
  hi := (7339 / 14214)
  vmin := (50455625 / 202037796)
  damping := (50455625 / 202037796)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell128
