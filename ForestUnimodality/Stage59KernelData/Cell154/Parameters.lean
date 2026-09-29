import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell154
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (57335933199482923373424510557 / 200000000000000000000000000000)
  probabilityCap := (11 / 21)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1531 / 1395)
def activityUpper : ℚ := (11 / 10)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3856164445395827617858231 / 1000000000000000000000000)
  B := (-1002778435496399916937449 / 10000000000000000000000000)
  C := (2893135030367108839755019 / 10000000000000000000000000)
  dδ := (818440684879221946879113 / 5000000000000000000000000)
  dM := (0)
  wL := (449938739373 / 312500000000)
  wR := (1280098017003 / 500000000000)
  wC := (1 / 10000000000000)
  price := ![(8537632728631034950694811 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3}
  fixedPrice := fun j => if j = -1 then (1330055606356537900580861 / 50000000000000000000000) else if j = 0 then (2172014034956033512457907 / 100000000000000000000000) else if j = 1 then (643494234706359549136323 / 20000000000000000000000) else if j = 2 then (1896490312644904108196897 / 50000000000000000000000) else if j = 3 then (9412046646599732113713799 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6848625628462605935281541 / 250000000000000000000000000000) else if j = 0 then (354372817060671885473703 / 8000000000000000000000000000) else if j = 1 then (73859609486079275255056397 / 1000000000000000000000000000000) else if j = 2 then (22381699844266447046986787 / 200000000000000000000000000000) else if j = 3 then (132255499079756278004921923 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1531 / 2926)
  hi := (11 / 21)
  vmin := (110 / 441)
  damping := (110 / 441)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell154
