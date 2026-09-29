import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell088
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 18
  density := (277406601089086571533017377519 / 1000000000000000000000000000000)
  probabilityCap := (395 / 792)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (60, 17), (60, 18), (61, 17), (61, 18), (62, 18), (63, 18), (64, 18)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (197 / 199)
def activityUpper : ℚ := (395 / 397)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (23)
  A := (398124010919968535901603 / 125000000000000000000000)
  B := (-8758957415990772932268271 / 100000000000000000000000000)
  C := (3882747399760275858193737 / 1000000000000000000000000000)
  dδ := (1322476163100946844330963 / 10000000000000000000000000)
  dM := (0)
  wL := (0)
  wR := (36597481209 / 2500000000000)
  wC := (9963402518791 / 10000000000000)
  price := ![(6384660182813492568243419 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (987461349606611449303273 / 50000000000000000000000) else if j = 0 then (79466380108689254058163 / 5000000000000000000000) else if j = 1 then (61211855715165786051557 / 3125000000000000000000) else if j = 2 then (31174504994485204179 / 1600000000000000000) else if j = 3 then (1199098053231146110420013 / 100000000000000000000000) else if j = 4 then (1538631433538011705763893 / 100000000000000000000000) else if j = 5 then (260974995766439921141 / 25000000000000000000) else if j = 6 then (358260175163850647095387 / 25000000000000000000000) else if j = 7 then (1441461402826941018417983 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6554886793925639331755731 / 250000000000000000000000000000) else if j = 0 then (23650205013342788071378223 / 500000000000000000000000000000) else if j = 1 then (85551820477016638423870127 / 1000000000000000000000000000000) else if j = 2 then (27747878866369347793585113 / 200000000000000000000000000000) else if j = 3 then (36254886792236001003213359 / 200000000000000000000000000000) else if j = 4 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 5 then (189199674550135197056204477 / 1000000000000000000000000000000) else if j = 6 then (160225425280654811627977007 / 1000000000000000000000000000000) else if j = 7 then (55596001243405028519376109 / 500000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell088
