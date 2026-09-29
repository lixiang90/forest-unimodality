import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell085
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (55389495937292011283385574343 / 200000000000000000000000000000)
  probabilityCap := (197 / 396)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (131 / 133)
def activityUpper : ℚ := (197 / 199)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (26)
  A := (2963626461334885637711523 / 1000000000000000000000000)
  B := (-7639098597879508123487113 / 100000000000000000000000000)
  C := (105937603443421856502793 / 10000000000000000000000000)
  dδ := (638849586232936167418117 / 5000000000000000000000000)
  dM := (0)
  wL := (397512604277 / 312500000000)
  wR := (405308615347 / 312500000000)
  wC := (55897347547 / 156250000000)
  price := ![(2969439630814554309523601 / 500000000000000000000000), (4427352805342831265633663 / 5000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (557270115388342368589747 / 25000000000000000000000) else if j = 0 then (1684580683042053195208609 / 100000000000000000000000) else if j = 1 then (544410666294791667496611 / 25000000000000000000000) else if j = 2 then (115983859582780235442101 / 6250000000000000000000) else if j = 3 then (1281238740672071152459921 / 100000000000000000000000) else if j = 4 then (770786527869282434011211 / 50000000000000000000000) else if j = 5 then (4205977088083071357971221 / 500000000000000000000000) else if j = 6 then (589113358843586976121287 / 50000000000000000000000) else if j = 7 then (97258955238370539686521 / 15625000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13039972610887615958385679 / 500000000000000000000000000000) else if j = 0 then (23643394944624508322701637 / 500000000000000000000000000000) else if j = 1 then (17168163099359313627652723 / 200000000000000000000000000000) else if j = 2 then (17464816985341116974010203 / 125000000000000000000000000000) else if j = 3 then (183478097628740993347266579 / 1000000000000000000000000000000) else if j = 4 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 5 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 6 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 7 then (81909822801042291322270167 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (131 / 264)
  hi := (197 / 396)
  vmin := (17423 / 69696)
  damping := (17423 / 69696)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell085
