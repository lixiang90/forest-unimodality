import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell144
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (142829629203145994405459741547 / 500000000000000000000000000000)
  probabilityCap := (22647 / 43472)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (11311 / 10425)
def activityUpper : ℚ := (22647 / 20825)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1205718386217058027909843 / 500000000000000000000000)
  B := (-2628929014381146955781077 / 100000000000000000000000000)
  C := (1720976849163549093901793 / 10000000000000000000000000)
  dδ := (1436236419991648582961119 / 10000000000000000000000000)
  dM := (1021505983434333559786711 / 1000000000000000000000000000)
  wL := (1022926931533 / 625000000000)
  wR := (5908292273867 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(3057944584798771625600011 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (636265382317568306547173 / 25000000000000000000000) else if j = 0 then (825512337304704374219 / 32000000000000000000) else if j = 1 then (4065653070428955828674589 / 100000000000000000000000) else if j = 2 then (1414626128464194287914779 / 25000000000000000000000) else if j = 3 then (388345445369271935476263 / 6250000000000000000000) else if j = 4 then (5709126449852358398118213 / 1000000000000000000000000) else if j = 5 then (8529923254735647830671041 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (2706934147472135133765461 / 100000000000000000000000000000) else if j = 0 then (44274299825976021736633911 / 1000000000000000000000000000000) else if j = 1 then (74671574709818128640282781 / 1000000000000000000000000000000) else if j = 2 then (114440142427397486711550383 / 1000000000000000000000000000000) else if j = 3 then (13680314195547836176970229 / 100000000000000000000000000000) else if j = 4 then (13680314195547836176970229 / 100000000000000000000000000000) else if j = 5 then (13680314195547836176970229 / 100000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (11311 / 21736)
  hi := (22647 / 43472)
  vmin := (471623775 / 1889814784)
  damping := (471623775 / 1889814784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell144
