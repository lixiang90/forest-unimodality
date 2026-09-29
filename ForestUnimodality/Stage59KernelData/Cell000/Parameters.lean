import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell000
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (9 / 35)

def pairs : List (ℕ × ℕ) := [(59, 15), (60, 15), (63, 16), (64, 16), (67, 17), (68, 17), (70, 18), (71, 18), (72, 18), (74, 19), (75, 19), (76, 19), (78, 20), (79, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1 / 3)
def activityUpper : ℚ := (9 / 26)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (50)
  A := (-1496695659075925530123641 / 100000000000000000000000)
  B := (1532727295505132314445973 / 1000000000000000000000000)
  C := (-1790920565469041214612389 / 2000000000000000000000000)
  dδ := (7067887766303347918395161 / 10000000000000000000000000)
  dM := (1032252038837396489190379 / 50000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {1}
  fixedPrice := fun j => if j = 1 then (3485936677843564979184521 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (21389918080748606175948241 / 125000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1 / 4)
  hi := (9 / 35)
  vmin := (3 / 16)
  damping := (7500000000000000000000000000000000000000 / 98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell000
