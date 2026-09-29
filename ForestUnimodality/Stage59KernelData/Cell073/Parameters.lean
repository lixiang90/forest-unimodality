import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell073
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (2152722745353484154092563887 / 7812500000000000000000000000)
  probabilityCap := (3193 / 6468)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4777 / 4925)
def activityUpper : ℚ := (3193 / 3275)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1411909407430724198107441 / 500000000000000000000000)
  B := (-6284163631681796702288523 / 100000000000000000000000000)
  C := (-451005669953822522361131 / 25000000000000000000000000)
  dδ := (1268410819498049513232019 / 10000000000000000000000000)
  dM := (139937023223592779501423 / 500000000000000000000000000)
  wL := (641476254521 / 312500000000)
  wR := (4868189963831 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(6268581194235789411095539 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2214718915152492328957123 / 100000000000000000000000) else if j = 0 then (1713652419599353393664387 / 100000000000000000000000) else if j = 1 then (5689364306055534115103 / 250000000000000000000) else if j = 2 then (967994801080715561170109 / 50000000000000000000000) else if j = 3 then (271169711482265718416329 / 20000000000000000000000) else if j = 4 then (1834511084318759444045099 / 100000000000000000000000) else if j = 5 then (1596791601675328564624579 / 100000000000000000000000) else if j = 6 then (218445709087543482596061 / 12500000000000000000000) else if j = 7 then (932602311014907670028151 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25685338864013443885570327 / 1000000000000000000000000000000) else if j = 0 then (47287242880257873919637779 / 1000000000000000000000000000000) else if j = 1 then (86794751329438566905726807 / 1000000000000000000000000000000) else if j = 2 then (8927485218151763766416161 / 62500000000000000000000000000) else if j = 3 then (95230236933995951733208407 / 500000000000000000000000000000) else if j = 4 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 5 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 6 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 7 then (175322512233549477522801403 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell073
