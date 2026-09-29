import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell045
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (135098200109825166189862266671 / 500000000000000000000000000000)
  probabilityCap := (23 / 48)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (581 / 635)
def activityUpper : ℚ := (23 / 25)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (27)
  A := (-974333409808414582286673 / 500000000000000000000000)
  B := (2446019311454392941573843 / 10000000000000000000000000)
  C := (-8412425505447394813440809 / 100000000000000000000000000)
  dδ := (257238569353437529496631 / 2000000000000000000000000)
  dM := (5560451777709004075878063 / 1000000000000000000000000000)
  wL := (554589121313 / 250000000000)
  wR := (4454108786869 / 2500000000000)
  wC := (1 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1156356680414342541496353 / 50000000000000000000000) else if j = 0 then (2467288034658669815257781 / 100000000000000000000000) else if j = 1 then (530771553372038766838159 / 20000000000000000000000) else if j = 2 then (557622114710536465054247 / 25000000000000000000000) else if j = 3 then (370627528270104917851313 / 20000000000000000000000) else if j = 4 then (2617433094680103522478021 / 100000000000000000000000) else if j = 5 then (1846142076445255142402857 / 50000000000000000000000) else if j = 6 then (203932604767510134990971 / 5000000000000000000000) else if j = 7 then (2154451979202449685146803 / 250000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (42478681285716701039343767 / 1000000000000000000000000000000) else if j = 0 then (21171541764093281577976479 / 250000000000000000000000000000) else if j = 1 then (30683393861004755910110839 / 200000000000000000000000000000) else if j = 2 then (216784847931011862408391797 / 1000000000000000000000000000000) else if j = 3 then (244698615975640480143251611 / 1000000000000000000000000000000) else if j = 4 then (244698615975640480143251611 / 1000000000000000000000000000000) else if j = 5 then (244698615975640480143251611 / 1000000000000000000000000000000) else if j = 6 then (244698615975640480143251611 / 1000000000000000000000000000000) else if j = 7 then (244698615975640480143251611 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (581 / 1216)
  hi := (23 / 48)
  vmin := (368935 / 1478656)
  damping := (368935 / 1478656)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell045
