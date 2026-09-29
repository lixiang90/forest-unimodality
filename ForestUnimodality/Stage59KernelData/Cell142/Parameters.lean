import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell142
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (285453758047105653251015877733 / 1000000000000000000000000000000)
  probabilityCap := (11311 / 21736)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (22597 / 20875)
def activityUpper : ℚ := (11311 / 10425)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1915811020418136363275607 / 1000000000000000000000000)
  B := (-4883942931548992949508659 / 10000000000000000000000000000)
  C := (654849994134520663191523 / 5000000000000000000000000)
  dδ := (689027759782330911919601 / 5000000000000000000000000)
  dM := (1382600771117013229924431 / 1000000000000000000000000000)
  wL := (4265684106391 / 2500000000000)
  wR := (716789486701 / 312500000000)
  wC := (1 / 10000000000000)
  price := ![(2645269270665430383360217 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (1249689062432817721060019 / 50000000000000000000000) else if j = 0 then (670199826099120077316229 / 25000000000000000000000) else if j = 1 then (1056123512441302736419857 / 25000000000000000000000) else if j = 2 then (1453017156903507967058431 / 25000000000000000000000) else if j = 3 then (6104063937664125205628807 / 100000000000000000000000) else if j = 4 then (119493431157433978029303 / 10000000000000000000000) else if j = 5 then (323138887981661042658743 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (1687501430278220252624073 / 62500000000000000000000000000) else if j = 0 then (8852559823703162586861587 / 200000000000000000000000000000) else if j = 1 then (74824395029374223483306109 / 1000000000000000000000000000000) else if j = 2 then (28734724242670345969022271 / 250000000000000000000000000000) else if j = 3 then (137716329342689369196419177 / 1000000000000000000000000000000) else if j = 4 then (137716329342689369196419177 / 1000000000000000000000000000000) else if j = 5 then (137716329342689369196419177 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (22597 / 43472)
  hi := (11311 / 21736)
  vmin := (117917175 / 472453696)
  damping := (117917175 / 472453696)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell142
