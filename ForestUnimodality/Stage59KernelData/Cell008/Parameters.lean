import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell008
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 25
  density := (1 / 4)
  probabilityCap := (20 / 63)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (59, 18), (60, 15), (60, 16), (60, 17), (60, 18), (60, 19), (61, 16), (61, 17), (61, 18), (61, 19), (62, 16), (62, 17), (62, 18), (62, 19), (63, 16), (63, 17), (63, 18), (63, 19), (63, 20), (64, 16), (64, 17), (64, 18), (64, 19), (64, 20), (65, 17), (65, 18), (65, 19), (65, 20), (66, 17), (66, 18), (66, 19), (66, 20), (67, 17), (67, 18), (67, 19), (67, 20), (67, 21), (68, 17), (68, 18), (68, 19), (68, 20), (68, 21), (69, 18), (69, 19), (69, 20), (69, 21), (70, 18), (70, 19), (70, 20), (70, 21), (70, 22), (71, 18), (71, 19), (71, 20), (71, 21), (71, 22), (72, 18), (72, 19), (72, 20), (72, 21), (72, 22), (73, 19), (73, 20), (73, 21), (73, 22), (73, 23), (74, 19), (74, 20), (74, 21), (74, 22), (74, 23), (75, 19), (75, 20), (75, 21), (75, 22), (75, 23), (76, 19), (76, 20), (76, 21), (76, 22), (76, 23), (76, 24), (77, 20), (77, 21), (77, 22), (77, 23), (77, 24), (78, 20), (78, 21), (78, 22), (78, 23), (78, 24), (79, 20), (79, 21), (79, 22), (79, 23), (79, 24), (79, 25)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (13 / 29)
def activityUpper : ℚ := (20 / 43)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (44)
  A := (1064929300856108624785179 / 1000000000000000000000000)
  B := (2148720101673975285683227 / 50000000000000000000000000)
  C := (-222169773370312323423903 / 2000000000000000000000000)
  dδ := (6012457577132351155269063 / 100000000000000000000000000)
  dM := (7825543432865165929118723 / 100000000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := ![(7583240340007712632086623 / 1000000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := {1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = 1 then (61479370464259730511003 / 1250000000000000000000) else if j = 2 then (869797979751921523927649 / 50000000000000000000000) else if j = 3 then (532797086630420579922429 / 50000000000000000000000) else if j = 4 then (7156959345161458152517753 / 1000000000000000000000000) else if j = 5 then (3883550319163215913675913 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (94869422966788527366139783 / 250000000000000000000000000000) else if j = 2 then (407938518757190667674401067 / 500000000000000000000000000000) else if j = 3 then (1425235199907934895187438727 / 1000000000000000000000000000000) else if j = 4 then (1021418559934020008217664421 / 500000000000000000000000000000) else if j = 5 then (1209907043774080555715672431 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (13 / 42)
  hi := (20 / 63)
  vmin := (377 / 1764)
  damping := (3770000000000000000000000000000000000000000 / 43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell008
