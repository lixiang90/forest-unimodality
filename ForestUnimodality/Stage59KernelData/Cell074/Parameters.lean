import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell074
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (2152722745353484154092563887 / 7812500000000000000000000000)
  probabilityCap := (3193 / 6468)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4777 / 4925)
def activityUpper : ℚ := (3193 / 3275)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (30)
  A := (2982630391083390148821763 / 1000000000000000000000000)
  B := (-355446469987667212908633 / 5000000000000000000000000)
  C := (-538871627489771742869351 / 50000000000000000000000000)
  dδ := (966290567344576079023 / 8000000000000000000000)
  dM := (0)
  wL := (4436209557213 / 2500000000000)
  wR := (212590442759 / 125000000000)
  wC := (1311981587607 / 10000000000000)
  price := ![(7175701729983566146131579 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (510657523741638428305123 / 20000000000000000000000) else if j = 0 then (365390168328454265633809 / 20000000000000000000000) else if j = 1 then (647277994784566512720403 / 25000000000000000000000) else if j = 2 then (546592250465207030174497 / 25000000000000000000000) else if j = 3 then (753700419242981034528839 / 50000000000000000000000) else if j = 4 then (1894003008401983478847797 / 100000000000000000000000) else if j = 5 then (257328811382025124387951 / 25000000000000000000000) else if j = 6 then (332325710996611700664971 / 25000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25685338864013443885570327 / 1000000000000000000000000000000) else if j = 0 then (47287242880257873919637779 / 1000000000000000000000000000000) else if j = 1 then (86794751329438566905726807 / 1000000000000000000000000000000) else if j = 2 then (8927485218151763766416161 / 62500000000000000000000000000) else if j = 3 then (95230236933995951733208407 / 500000000000000000000000000000) else if j = 4 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 5 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 6 then (40573050186169707928444209 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (4777 / 9702)
  hi := (3193 / 6468)
  vmin := (23526725 / 94128804)
  damping := (23526725 / 94128804)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell074
