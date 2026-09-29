import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell033
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (133557186931568315609889186161 / 500000000000000000000000000000)
  probabilityCap := (841 / 1786)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 18), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 19), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1677 / 1895)
def activityUpper : ℚ := (841 / 945)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (4295854499423200107855791 / 1000000000000000000000000)
  B := (-209651548305262946936267 / 2000000000000000000000000)
  C := (-1924233524326391941983161 / 5000000000000000000000000)
  dδ := (1739607334612704170329067 / 10000000000000000000000000)
  dM := (0)
  wL := (6864086400359 / 2500000000000)
  wR := (78397839991 / 62500000000)
  wC := (1 / 10000000000000)
  price := ![(1986437315173634310383477 / 250000000000000000000000), (1251238281322041290266611 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (331929232670510820923937 / 25000000000000000000000) else if j = 1 then (2944774470563186241633957 / 100000000000000000000000) else if j = 2 then (1073629338475247863016193 / 50000000000000000000000) else if j = 3 then (37268476114372234064831 / 2000000000000000000000) else if j = 4 then (1640188364544474808326413 / 100000000000000000000000) else if j = 5 then (2115167653241063305813441 / 100000000000000000000000) else if j = 6 then (1122638525923312080578853 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (41019402541813779506614059 / 1000000000000000000000000000000) else if j = 1 then (1979014593573645600410147 / 12500000000000000000000000000) else if j = 2 then (5781734668740127515110263 / 25000000000000000000000000000) else if j = 3 then (269863642317578621692194933 / 1000000000000000000000000000000) else if j = 4 then (269863642317578621692194933 / 1000000000000000000000000000000) else if j = 5 then (269863642317578621692194933 / 1000000000000000000000000000000) else if j = 6 then (269863642317578621692194933 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1677 / 3572)
  hi := (841 / 1786)
  vmin := (3177915 / 12759184)
  damping := (3177915 / 12759184)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell033
