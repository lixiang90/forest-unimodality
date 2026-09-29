import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell097
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (69580866157077100115074798619 / 250000000000000000000000000000)
  probabilityCap := (405 / 808)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1)
def activityUpper : ℚ := (405 / 403)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (-1687840736843391609696141 / 5000000000000000000000000)
  B := (550868413155614217169287 / 5000000000000000000000000)
  C := (2954725783278817560773 / 200000000000000000000000)
  dδ := (1240114008321305805182533 / 10000000000000000000000000)
  dM := (170020977007127654587193 / 62500000000000000000000000)
  wL := (31337503123 / 2500000000000)
  wR := (157715886891 / 2500000000000)
  wC := (4905473304993 / 5000000000000)
  price := ![(11668474437208708138769 / 8000000000000000000000), (799698514926001813307721 / 200000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (24445731094903845104227 / 1000000000000000000000) else if j = 0 then (317240688239101729095637 / 20000000000000000000000) else if j = 1 then (2371747345859457212213783 / 100000000000000000000000) else if j = 2 then (994936860850723547855523 / 50000000000000000000000) else if j = 3 then (651209733862592266007141 / 50000000000000000000000) else if j = 4 then (1384426654622284047491121 / 100000000000000000000000) else if j = 5 then (724533537097898605594537 / 100000000000000000000000) else if j = 6 then (1064521315140491886097607 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26442155033863206344232833 / 1000000000000000000000000000000) else if j = 0 then (11806826631393013903359027 / 250000000000000000000000000000) else if j = 1 then (84805623573779680087366159 / 1000000000000000000000000000000) else if j = 2 then (136540759743062848971401673 / 1000000000000000000000000000000) else if j = 3 then (88313214851099538982860909 / 500000000000000000000000000000) else if j = 4 then (182513977358939047231245879 / 1000000000000000000000000000000) else if j = 5 then (182513977358939047231245879 / 1000000000000000000000000000000) else if j = 6 then (182513977358939047231245879 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (405 / 808)
  vmin := (163215 / 652864)
  damping := (163215 / 652864)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell097
