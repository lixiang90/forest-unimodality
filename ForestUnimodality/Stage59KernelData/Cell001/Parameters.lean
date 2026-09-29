import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell001
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (37 / 140)

def pairs : List (ℕ × ℕ) := [(59, 15), (60, 15), (61, 16), (62, 16), (63, 16), (64, 16), (65, 17), (66, 17), (67, 17), (68, 17), (69, 18), (70, 18), (71, 18), (72, 18), (72, 19), (73, 19), (74, 19), (75, 19), (76, 19), (76, 20), (77, 20), (78, 20), (79, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9 / 26)
def activityUpper : ℚ := (37 / 103)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (49)
  A := (-316119367040789727388983 / 6250000000000000000000)
  B := (3078042743336401709797201 / 1000000000000000000000000)
  C := (-2845117826182736453510813 / 5000000000000000000000000)
  dδ := (4504471807962037721573267 / 10000000000000000000000000)
  dM := (3842821119681843339277449 / 100000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {1}
  fixedPrice := fun j => if j = 1 then (1007157637184461218549103 / 5000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (24154421175699545790729217 / 125000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9 / 35)
  hi := (37 / 140)
  vmin := (234 / 1225)
  damping := (374400000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell001
