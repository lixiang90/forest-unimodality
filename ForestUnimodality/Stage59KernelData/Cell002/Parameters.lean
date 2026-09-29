import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell002
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (19 / 70)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (60, 15), (60, 16), (61, 16), (62, 16), (63, 16), (63, 17), (64, 16), (64, 17), (65, 17), (66, 17), (67, 17), (67, 18), (68, 17), (68, 18), (69, 18), (70, 18), (70, 19), (71, 18), (71, 19), (72, 18), (72, 19), (73, 19), (74, 19), (74, 20), (75, 19), (75, 20), (76, 19), (76, 20), (77, 20), (78, 20), (78, 21), (79, 20), (79, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (37 / 103)
def activityUpper : ℚ := (19 / 51)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (49)
  A := (79606104810975028036637 / 40000000000000000000000)
  B := (167183769469613302538491 / 4000000000000000000000000)
  C := (-570905837671541946387599 / 2500000000000000000000000)
  dδ := (768796318000968398331807 / 5000000000000000000000000)
  dM := (3990406789643488561988849 / 10000000000000000000000000000)
  wL := (2964726250743 / 2500000000000)
  wR := (0)
  wC := (7035273749257 / 10000000000000)
  price := ![(1412042810399618986139103 / 250000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (30889426821503427333937 / 1000000000000000000000) else if j = 0 then (295880493702276510248339 / 10000000000000000000000) else if j = 1 then (924100916106383323267437 / 20000000000000000000000) else if j = 2 then (19612240866112657933229 / 1250000000000000000000) else if j = 3 then (2352826541778149760375527 / 250000000000000000000000) else if j = 4 then (2262239457659796393329543 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (599891489596927988449363 / 40000000000000000000000000000) else if j = 0 then (64409402040933320865089499 / 1000000000000000000000000000000) else if j = 1 then (43222098737994728475257427 / 200000000000000000000000000000) else if j = 2 then (116017212401985850117796251 / 200000000000000000000000000000) else if j = 3 then (316280476243900570016854089 / 250000000000000000000000000000) else if j = 4 then (1131951178136065197955056739 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (37 / 140)
  hi := (19 / 70)
  vmin := (3811 / 19600)
  damping := (381100000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell002
