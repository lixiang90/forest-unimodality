import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell005
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (37 / 126)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (60, 15), (60, 16), (60, 17), (61, 16), (61, 17), (62, 16), (62, 17), (62, 18), (63, 16), (63, 17), (63, 18), (64, 16), (64, 17), (64, 18), (65, 17), (65, 18), (65, 19), (66, 17), (66, 18), (66, 19), (67, 17), (67, 18), (67, 19), (68, 17), (68, 18), (68, 19), (69, 18), (69, 19), (69, 20), (70, 18), (70, 19), (70, 20), (71, 18), (71, 19), (71, 20), (72, 18), (72, 19), (72, 20), (72, 21), (73, 19), (73, 20), (73, 21), (74, 19), (74, 20), (74, 21), (75, 19), (75, 20), (75, 21), (75, 22), (76, 19), (76, 20), (76, 21), (76, 22), (77, 20), (77, 21), (77, 22), (78, 20), (78, 21), (78, 22), (79, 20), (79, 21), (79, 22), (79, 23)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (2 / 5)
def activityUpper : ℚ := (37 / 89)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (46)
  A := (-1321195319705312114183471 / 50000000000000000000000)
  B := (1930301329450881508975613 / 1000000000000000000000000)
  C := (-1170521593560753526030993 / 1250000000000000000000000)
  dδ := (373909322659004769717761 / 625000000000000000000000)
  dM := (126158121909174716218649 / 5000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {1}
  fixedPrice := fun j => if j = 1 then (260731684465300723729797 / 10000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (1511795274522660950133481 / 5000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell005
