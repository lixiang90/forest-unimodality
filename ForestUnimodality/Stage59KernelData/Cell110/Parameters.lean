import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell110
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (280553856589125894230675227333 / 1000000000000000000000000000000)
  probabilityCap := (5227 / 10302)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (10429 / 10175)
def activityUpper : ℚ := (5227 / 5075)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (1899866814267867220493713 / 5000000000000000000000000)
  B := (1795527347449178690030891 / 25000000000000000000000000)
  C := (2071688080101271450805811 / 25000000000000000000000000)
  dδ := (134890263269508342558467 / 1000000000000000000000000)
  dM := (14523675641917659323403 / 6250000000000000000000000)
  wL := (993430262371 / 2500000000000)
  wR := (340337606423 / 500000000000)
  wC := (3652440852757 / 5000000000000)
  price := ![(4761077211026514710567881 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (484003093104213846231687 / 20000000000000000000000) else if j = 0 then (2114944838132153037690841 / 100000000000000000000000) else if j = 1 then (38939813626822739056621 / 1562500000000000000000) else if j = 2 then (11268613372038001330111 / 400000000000000000000) else if j = 3 then (1320302394856945582546359 / 100000000000000000000000) else if j = 4 then (1197739680272339768407619 / 100000000000000000000000) else if j = 5 then (9384832663618894343926513 / 1000000000000000000000000) else if j = 6 then (3275374908980280164172427 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26685643196168176168996747 / 1000000000000000000000000000000) else if j = 0 then (9279491464843198748434961 / 200000000000000000000000000000) else if j = 1 then (16602771502649094115224643 / 200000000000000000000000000000) else if j = 2 then (131308626203766418292493211 / 1000000000000000000000000000000) else if j = 3 then (10358578790168224419895781 / 62500000000000000000000000000) else if j = 4 then (167106798572241874425538331 / 1000000000000000000000000000000) else if j = 5 then (167106798572241874425538331 / 1000000000000000000000000000000) else if j = 6 then (167106798572241874425538331 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (10429 / 20604)
  hi := (5227 / 10302)
  vmin := (26527025 / 106131204)
  damping := (26527025 / 106131204)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell110
