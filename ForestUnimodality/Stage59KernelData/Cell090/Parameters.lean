import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell090
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (277406601089086571533017377519 / 1000000000000000000000000000000)
  probabilityCap := (395 / 792)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 20), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (197 / 199)
def activityUpper : ℚ := (395 / 397)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (2886446028337568720957051 / 1000000000000000000000000)
  B := (-6773468870978198441701323 / 100000000000000000000000000)
  C := (1669315805558018936394227 / 100000000000000000000000000)
  dδ := (60663745426514058267653 / 500000000000000000000000)
  dM := (0)
  wL := (0)
  wR := (35330438513 / 625000000000)
  wC := (2464669561487 / 2500000000000)
  price := ![(3519756116527538836180611 / 500000000000000000000000), (1470002496197589936244299 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2700443656095790245785793 / 100000000000000000000000) else if j = 0 then (1096675892909626170990123 / 50000000000000000000000) else if j = 1 then (1307860138765177993036559 / 50000000000000000000000) else if j = 2 then (113217561461332234529209 / 5000000000000000000000) else if j = 3 then (81356241692931270392819 / 5000000000000000000000) else if j = 4 then (388701026270547558283397 / 20000000000000000000000) else if j = 5 then (168231950804891483564063 / 12500000000000000000000) else if j = 6 then (876397407775863968026897 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6554886793925639331755731 / 250000000000000000000000000000) else if j = 0 then (23650205013342788071378223 / 500000000000000000000000000000) else if j = 1 then (85551820477016638423870127 / 1000000000000000000000000000000) else if j = 2 then (27747878866369347793585113 / 200000000000000000000000000000) else if j = 3 then (36254886792236001003213359 / 200000000000000000000000000000) else if j = 4 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 5 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 6 then (189199674550135197056204477 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (197 / 396)
  hi := (395 / 792)
  vmin := (39203 / 156816)
  damping := (39203 / 156816)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell090
