import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell140
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (17828010889862884013025818133 / 62500000000000000000000000000)
  probabilityCap := (22597 / 43472)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (27 / 25)
def activityUpper : ℚ := (22597 / 20875)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1004718771038837291598611 / 500000000000000000000000)
  B := (-827107466666129019505771 / 125000000000000000000000000)
  C := (51484063408751723489587 / 400000000000000000000000)
  dδ := (275138276488378463735529 / 2000000000000000000000000)
  dM := (127862350067674528791839 / 100000000000000000000000000)
  wL := (856020125153 / 500000000000)
  wR := (2859949687117 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(5422188751100357251289097 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (623011684134606191776129 / 25000000000000000000000) else if j = 0 then (2642828311708772659471833 / 100000000000000000000000) else if j = 1 then (4111886692057783676546023 / 100000000000000000000000) else if j = 2 then (5541953929684993340742949 / 100000000000000000000000) else if j = 3 then (5628790196406636425763281 / 100000000000000000000000) else if j = 4 then (1186798583358002545651289 / 100000000000000000000000) else if j = 5 then (62624319003924100002223 / 4000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (1683133430873272359661681 / 62500000000000000000000000000) else if j = 0 then (22125032271194804058260023 / 500000000000000000000000000000) else if j = 1 then (74975416203801314758036383 / 1000000000000000000000000000000) else if j = 2 then (115436548601905300524701619 / 1000000000000000000000000000000) else if j = 3 then (69315823730676751183544059 / 500000000000000000000000000000) else if j = 4 then (69315823730676751183544059 / 500000000000000000000000000000) else if j = 5 then (69315823730676751183544059 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (22597 / 43472)
  vmin := (471712375 / 1889814784)
  damping := (471712375 / 1889814784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell140
