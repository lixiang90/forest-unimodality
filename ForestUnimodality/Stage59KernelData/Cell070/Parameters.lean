import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell070
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (137539039664402802851605377441 / 500000000000000000000000000000)
  probabilityCap := (4777 / 9702)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9529 / 9875)
def activityUpper : ℚ := (4777 / 4925)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (292975676111059538209247 / 100000000000000000000000)
  B := (-1738339780788043451020819 / 25000000000000000000000000)
  C := (-3113020192052149900940883 / 50000000000000000000000000)
  dδ := (1239283755297420075436321 / 10000000000000000000000000)
  dM := (0)
  wL := (2662695756753 / 1250000000000)
  wR := (4674608486493 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1663855924158025523240667 / 250000000000000000000000), (1263020163040756260741659 / 1000000000000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (469948500587845074960569 / 20000000000000000000000) else if j = 0 then (1088427031820029178277309 / 100000000000000000000000) else if j = 1 then (1314502716215942434985209 / 50000000000000000000000) else if j = 2 then (215964461813314940741293 / 10000000000000000000000) else if j = 3 then (1384089642260490471414869 / 100000000000000000000000) else if j = 4 then (1791257823877231913911601 / 100000000000000000000000) else if j = 5 then (1257438820145758029411809 / 100000000000000000000000) else if j = 6 then (3991421830795068181885199 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25530861305273956186250903 / 1000000000000000000000000000000) else if j = 0 then (47245752144860191667238547 / 1000000000000000000000000000000) else if j = 1 then (43521986777143632425845031 / 500000000000000000000000000000) else if j = 2 then (143787402478813570867700419 / 1000000000000000000000000000000) else if j = 3 then (192714851239397924948807187 / 1000000000000000000000000000000) else if j = 4 then (103163625962379587567300187 / 500000000000000000000000000000) else if j = 5 then (103163625962379587567300187 / 500000000000000000000000000000) else if j = 6 then (103163625962379587567300187 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9529 / 19404)
  hi := (4777 / 9702)
  vmin := (94098875 / 376515216)
  damping := (94098875 / 376515216)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell070
