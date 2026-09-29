import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell009
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (41 / 126)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (59, 18), (59, 19), (60, 15), (60, 16), (60, 17), (60, 18), (60, 19), (61, 16), (61, 17), (61, 18), (61, 19), (62, 16), (62, 17), (62, 18), (62, 19), (62, 20), (63, 16), (63, 17), (63, 18), (63, 19), (63, 20), (64, 16), (64, 17), (64, 18), (64, 19), (64, 20), (65, 17), (65, 18), (65, 19), (65, 20), (65, 21), (66, 17), (66, 18), (66, 19), (66, 20), (66, 21), (67, 17), (67, 18), (67, 19), (67, 20), (67, 21), (68, 17), (68, 18), (68, 19), (68, 20), (68, 21), (68, 22), (69, 18), (69, 19), (69, 20), (69, 21), (69, 22), (70, 18), (70, 19), (70, 20), (70, 21), (70, 22), (71, 18), (71, 19), (71, 20), (71, 21), (71, 22), (71, 23), (72, 18), (72, 19), (72, 20), (72, 21), (72, 22), (72, 23), (73, 19), (73, 20), (73, 21), (73, 22), (73, 23), (74, 19), (74, 20), (74, 21), (74, 22), (74, 23), (74, 24), (75, 19), (75, 20), (75, 21), (75, 22), (75, 23), (75, 24), (76, 19), (76, 20), (76, 21), (76, 22), (76, 23), (76, 24), (77, 20), (77, 21), (77, 22), (77, 23), (77, 24), (78, 20), (78, 21), (78, 22), (78, 23), (78, 24), (79, 20), (79, 21), (79, 22), (79, 23), (79, 24)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (20 / 43)
def activityUpper : ℚ := (41 / 85)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (44)
  A := (-7469742629525930903810149 / 1000000000000000000000000)
  B := (6358651548062124181370791 / 10000000000000000000000000)
  C := (-49038295925645410122673 / 312500000000000000000000)
  dδ := (2199573322036568745474483 / 25000000000000000000000000)
  dM := (4806958560412451751664431 / 500000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {1, 2, 3}
  fixedPrice := fun j => if j = 1 then (4955519416047181380235997 / 100000000000000000000000) else if j = 2 then (418318715094624771211329 / 25000000000000000000000) else if j = 3 then (38442357031523327615119 / 6250000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (50273640765798685945925281 / 125000000000000000000000000000) else if j = 2 then (416903362448086663941819403 / 500000000000000000000000000000) else if j = 3 then (702253377294414273865412257 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (20 / 63)
  hi := (41 / 126)
  vmin := (860 / 3969)
  damping := (34400000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell009
