import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell078
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (17251153016544075690277703103 / 62500000000000000000000000000)
  probabilityCap := (49 / 99)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 18), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 20), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 21), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (3193 / 3275)
def activityUpper : ℚ := (49 / 50)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (1378398775803202428392069 / 500000000000000000000000)
  B := (-1598245927154614068332883 / 25000000000000000000000000)
  C := (674019825457028345233601 / 250000000000000000000000000)
  dδ := (1209815881507671359029743 / 10000000000000000000000000)
  dM := (0)
  wL := (876232106387 / 625000000000)
  wR := (432439493679 / 312500000000)
  wC := (151777781251 / 500000000000)
  price := ![(1281519828425115647974053 / 200000000000000000000000), (663439446072430438761103 / 500000000000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2602979025752143016347873 / 100000000000000000000000) else if j = 0 then (1754814501826594863587161 / 100000000000000000000000) else if j = 1 then (2582531311637921334067869 / 100000000000000000000000) else if j = 2 then (1078102992599676035467837 / 50000000000000000000000) else if j = 3 then (11495891160237881933881 / 800000000000000000000) else if j = 4 then (6570611591112424099137 / 390625000000000000000) else if j = 5 then (206878890249544156176853 / 25000000000000000000000) else if j = 6 then (134154056544937949624341 / 12500000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (807404209768817755918701 / 31250000000000000000000000000) else if j = 0 then (1892871842070167797390521 / 40000000000000000000000000000) else if j = 1 then (43266858166241311086588127 / 500000000000000000000000000000) else if j = 2 then (5675128138729350665203631 / 40000000000000000000000000000) else if j = 3 then (94102890055461171744447963 / 500000000000000000000000000000) else if j = 4 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 5 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 6 then (199433126491165748594983909 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (3193 / 6468)
  hi := (49 / 99)
  vmin := (10457075 / 41835024)
  damping := (10457075 / 41835024)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell078
