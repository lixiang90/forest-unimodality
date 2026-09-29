import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell072
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 18
  density := (2152722745353484154092563887 / 7812500000000000000000000000)
  probabilityCap := (3193 / 6468)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (60, 17), (60, 18), (61, 17), (61, 18), (62, 18), (63, 18), (64, 18), (65, 18)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4777 / 4925)
def activityUpper : ℚ := (3193 / 3275)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (3068756461569505018417203 / 1000000000000000000000000)
  B := (-7663360316541691086289489 / 100000000000000000000000000)
  C := (-2387324563565030796641331 / 50000000000000000000000000)
  dδ := (169517683040498155777609 / 1250000000000000000000000)
  dM := (971888447141969246192983 / 5000000000000000000000000000)
  wL := (5256379305973 / 2500000000000)
  wR := (2371810347013 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(311004432031181821116661 / 50000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (496937949196070771762379 / 25000000000000000000000) else if j = 0 then (7411861503998107281177 / 500000000000000000000) else if j = 1 then (539401503244273428094857 / 25000000000000000000000) else if j = 2 then (91873983700192614065827 / 5000000000000000000000) else if j = 3 then (1282401712295215467918297 / 100000000000000000000000) else if j = 4 then (185537865104892460976771 / 10000000000000000000000) else if j = 5 then (32733209022857828740527 / 1562500000000000000000) else if j = 6 then (891079223923018304276411 / 50000000000000000000000) else if j = 7 then (1119297909531943702177159 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25685338864013443885570327 / 1000000000000000000000000000000) else if j = 0 then (47287242880257873919637779 / 1000000000000000000000000000000) else if j = 1 then (86794751329438566905726807 / 1000000000000000000000000000000) else if j = 2 then (8927485218151763766416161 / 62500000000000000000000000000) else if j = 3 then (95230236933995951733208407 / 500000000000000000000000000000) else if j = 4 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 5 then (40573050186169707928444209 / 200000000000000000000000000000) else if j = 6 then (175322512233549477522801403 / 1000000000000000000000000000000) else if j = 7 then (6208244075351349539814797 / 50000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell072
