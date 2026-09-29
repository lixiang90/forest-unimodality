import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell132
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (284417044314334994308742645149 / 1000000000000000000000000000000)
  probabilityCap := (7427 / 14352)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (107 / 100)
def activityUpper : ℚ := (7427 / 6925)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (9519886685897354382532853 / 10000000000000000000000000)
  B := (772957335377726789671371 / 12500000000000000000000000)
  C := (559208881134940979928949 / 5000000000000000000000000)
  dδ := (340343054253437957146211 / 2500000000000000000000000)
  dM := (2503247582998886257288351 / 1000000000000000000000000000)
  wL := (2188879563709 / 1250000000000)
  wR := (5622240872581 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(794186197034856622423149 / 200000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (78062771775070327606727 / 3125000000000000000000) else if j = 0 then (2791286315863252553981511 / 100000000000000000000000) else if j = 1 then (2114244659068925358269553 / 50000000000000000000000) else if j = 2 then (5009128817696102231593613 / 100000000000000000000000) else if j = 3 then (208195019504903200413537 / 12500000000000000000000) else if j = 4 then (1585386184165949252644623 / 100000000000000000000000) else if j = 5 then (196774118084967177821909 / 10000000000000000000000) else if j = 6 then (64035553794111130798683 / 5000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13326432403799182801851243 / 500000000000000000000000000000) else if j = 0 then (22101407685382958609333361 / 500000000000000000000000000000) else if j = 1 then (75593693152440871772408423 / 1000000000000000000000000000000) else if j = 2 then (23494741038582336386334919 / 200000000000000000000000000000) else if j = 3 then (142393568197009211874229237 / 1000000000000000000000000000000) else if j = 4 then (142393568197009211874229237 / 1000000000000000000000000000000) else if j = 5 then (142393568197009211874229237 / 1000000000000000000000000000000) else if j = 6 then (142393568197009211874229237 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (107 / 207)
  hi := (7427 / 14352)
  vmin := (51431975 / 205979904)
  damping := (51431975 / 205979904)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell132
