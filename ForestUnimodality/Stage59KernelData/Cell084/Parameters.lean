import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell084
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 18
  density := (55389495937292011283385574343 / 200000000000000000000000000000)
  probabilityCap := (197 / 396)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (60, 17), (60, 18), (61, 17), (61, 18), (62, 18), (63, 18), (64, 18)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (131 / 133)
def activityUpper : ℚ := (197 / 199)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (23)
  A := (3192782147076385219520489 / 1000000000000000000000000)
  B := (-4385774982341948680097943 / 50000000000000000000000000)
  C := (-390785990872234679192887 / 62500000000000000000000000)
  dδ := (26357685755266002658459 / 200000000000000000000000)
  dM := (0)
  wL := (1669150677947 / 1250000000000)
  wR := (325181318563 / 250000000000)
  wC := (852471364619 / 2500000000000)
  price := ![(3197027600362643440234933 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1958759006435132832280033 / 100000000000000000000000) else if j = 0 then (1523393465545178671050053 / 100000000000000000000000) else if j = 1 then (989102661859035414693153 / 50000000000000000000000) else if j = 2 then (849968731660727350174511 / 50000000000000000000000) else if j = 3 then (238565550558360790489587 / 20000000000000000000000) else if j = 4 then (1563445262687983650096157 / 100000000000000000000000) else if j = 5 then (1206137365051317722475233 / 100000000000000000000000) else if j = 6 then (174947411697386057127801 / 12500000000000000000000) else if j = 7 then (1458752777133489075822581 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13039972610887615958385679 / 500000000000000000000000000000) else if j = 0 then (23643394944624508322701637 / 500000000000000000000000000000) else if j = 1 then (17168163099359313627652723 / 200000000000000000000000000000) else if j = 2 then (17464816985341116974010203 / 125000000000000000000000000000) else if j = 3 then (183478097628740993347266579 / 1000000000000000000000000000000) else if j = 4 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 5 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 6 then (81909822801042291322270167 / 500000000000000000000000000000) else if j = 7 then (57130962942327177087360543 / 500000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell084
