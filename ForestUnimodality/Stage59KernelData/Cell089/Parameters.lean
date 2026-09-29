import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell089
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (277406601089086571533017377519 / 1000000000000000000000000000000)
  probabilityCap := (395 / 792)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (197 / 199)
def activityUpper : ℚ := (395 / 397)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (26)
  A := (1489704284357574585129669 / 500000000000000000000000)
  B := (-7702164889430364314026889 / 100000000000000000000000000)
  C := (850438801791392716411533 / 50000000000000000000000000)
  dδ := (1285749301155890977899077 / 10000000000000000000000000)
  dM := (0)
  wL := (0)
  wR := (75557887771 / 1250000000000)
  wC := (4924442112229 / 5000000000000)
  price := ![(5967777258529100237183229 / 1000000000000000000000000), (182152473423469785096529 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (447043119009266618490983 / 20000000000000000000000) else if j = 0 then (1709328732449821330874329 / 100000000000000000000000) else if j = 1 then (539910069314458684885949 / 25000000000000000000000) else if j = 2 then (1847805981435551458957889 / 100000000000000000000000) else if j = 3 then (320196434362048698574199 / 25000000000000000000000) else if j = 4 then (748451775929772011863861 / 50000000000000000000000) else if j = 5 then (1034823997938543849173243 / 125000000000000000000000) else if j = 6 then (1068939788418411396264673 / 100000000000000000000000) else if j = 7 then (872966922368664133280447 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6554886793925639331755731 / 250000000000000000000000000000) else if j = 0 then (23650205013342788071378223 / 500000000000000000000000000000) else if j = 1 then (85551820477016638423870127 / 1000000000000000000000000000000) else if j = 2 then (27747878866369347793585113 / 200000000000000000000000000000) else if j = 3 then (36254886792236001003213359 / 200000000000000000000000000000) else if j = 4 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 5 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 6 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 7 then (160225425280654811627977007 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell089
