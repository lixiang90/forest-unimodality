import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell004
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 25
  density := (1 / 4)
  probabilityCap := (2 / 7)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (60, 15), (60, 16), (60, 17), (61, 16), (61, 17), (62, 16), (62, 17), (63, 16), (63, 17), (63, 18), (64, 16), (64, 17), (64, 18), (65, 17), (65, 18), (66, 17), (66, 18), (67, 17), (67, 18), (67, 19), (68, 17), (68, 18), (68, 19), (69, 18), (69, 19), (70, 18), (70, 19), (70, 20), (71, 18), (71, 19), (71, 20), (72, 18), (72, 19), (72, 20), (73, 19), (73, 20), (74, 19), (74, 20), (74, 21), (75, 19), (75, 20), (75, 21), (76, 19), (76, 20), (76, 21), (77, 20), (77, 21), (77, 22), (78, 20), (78, 21), (78, 22), (79, 20), (79, 21), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (39 / 101)
def activityUpper : ℚ := (2 / 5)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (47)
  A := (4364890408210673714506811 / 500000000000000000000000)
  B := (1662754019869284172195023 / 10000000000000000000000000)
  C := (-5648747011927727212921013 / 10000000000000000000000000)
  dδ := (7550526651895843599504587 / 10000000000000000000000000)
  dM := (2864981034841590935152711 / 1000000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := ![(988267943224736995944113 / 2000000000000000000000)]
  retention := ![(1 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def countBound : ℤ → ℚ := fun _ => 0

def interval : IntervalWitness where
  lo := (39 / 140)
  hi := (2 / 7)
  vmin := (3939 / 19600)
  damping := (393900000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell004
