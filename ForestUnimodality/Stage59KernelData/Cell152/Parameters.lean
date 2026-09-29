import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell152
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (286476527424703293081212469329 / 1000000000000000000000000000000)
  probabilityCap := (1531 / 2926)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (2294 / 2095)
def activityUpper : ℚ := (1531 / 1395)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3609586718037810866178461 / 1000000000000000000000000)
  B := (-9305867304153284114143219 / 100000000000000000000000000)
  C := (2451466153533140845954819 / 10000000000000000000000000)
  dδ := (194339268242487428484111 / 1250000000000000000000000)
  dM := (0)
  wL := (151264227689 / 100000000000)
  wR := (3109197153887 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(398383688280742198628559 / 50000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (1305541387349433968267931 / 50000000000000000000000) else if j = 0 then (583655951891674273923627 / 25000000000000000000000) else if j = 1 then (3675325069378779119233513 / 100000000000000000000000) else if j = 2 then (5255706204649305846032803 / 100000000000000000000000) else if j = 3 then (6254725690761183187760253 / 100000000000000000000000) else if j = 4 then (437372795568559435963607 / 200000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13664375094283904590742119 / 500000000000000000000000000000) else if j = 0 then (22145652106914644023876701 / 500000000000000000000000000000) else if j = 1 then (37009802569376750301521883 / 500000000000000000000000000000) else if j = 2 then (56203651844416031646661253 / 500000000000000000000000000000) else if j = 3 then (133148690554994739897087109 / 1000000000000000000000000000000) else if j = 4 then (133148690554994739897087109 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (2294 / 4389)
  hi := (1531 / 2926)
  vmin := (2135745 / 8561476)
  damping := (2135745 / 8561476)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell152
