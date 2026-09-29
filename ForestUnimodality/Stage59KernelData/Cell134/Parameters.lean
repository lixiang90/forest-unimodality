import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell134
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (284624954835464599161975806289 / 1000000000000000000000000000000)
  probabilityCap := (11153 / 21528)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (7427 / 6925)
def activityUpper : ℚ := (11153 / 10375)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (9614728586660470653910693 / 10000000000000000000000000)
  B := (3021123454455202153590143 / 50000000000000000000000000)
  C := (1045281032932080106379047 / 10000000000000000000000000)
  dδ := (339388462749939806561983 / 2500000000000000000000000)
  dM := (616307292229957537875451 / 250000000000000000000000000)
  wL := (440419124201 / 250000000000)
  wR := (5595808757989 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1977851080697783814343893 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2484590534589109012131303 / 100000000000000000000000) else if j = 0 then (1392678612087918388340313 / 50000000000000000000000) else if j = 1 then (527879728786438207066567 / 12500000000000000000000) else if j = 2 then (5009323720364155008155649 / 100000000000000000000000) else if j = 3 then (169840500770626832149901 / 10000000000000000000000) else if j = 4 then (13113286679627311759333 / 781250000000000000000) else if j = 5 then (65678795507629339489597 / 3125000000000000000000) else if j = 6 then (1681365523424958396958573 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26725725665321571029147469 / 1000000000000000000000000000000) else if j = 0 then (44220697700022922141593003 / 1000000000000000000000000000000) else if j = 1 then (9431076875036109647706097 / 125000000000000000000000000000) else if j = 2 then (116975907921336127911713747 / 1000000000000000000000000000000) else if j = 3 then (141460822925582446445731119 / 1000000000000000000000000000000) else if j = 4 then (141460822925582446445731119 / 1000000000000000000000000000000) else if j = 5 then (141460822925582446445731119 / 1000000000000000000000000000000) else if j = 6 then (141460822925582446445731119 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (7427 / 14352)
  hi := (11153 / 21528)
  vmin := (115712375 / 463454784)
  damping := (115712375 / 463454784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell134
