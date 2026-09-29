import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell096
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (69580866157077100115074798619 / 250000000000000000000000000000)
  probabilityCap := (405 / 808)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1)
def activityUpper : ℚ := (405 / 403)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (25)
  A := (-894998304090543525035173 / 500000000000000000000000)
  B := (2331308683964763428519973 / 10000000000000000000000000)
  C := (1258114111342065882803709 / 50000000000000000000000000)
  dδ := (388740761535928246867 / 3125000000000000000000)
  dM := (2778760781838272853061511 / 500000000000000000000000000)
  wL := (877157451941 / 2500000000000)
  wR := (275465886639 / 625000000000)
  wC := (8020979001503 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2362221030243869890341557 / 100000000000000000000000) else if j = 0 then (712836104708317819245167 / 25000000000000000000000) else if j = 1 then (1214918462901166940071107 / 25000000000000000000000) else if j = 2 then (6423402056188956521509681 / 100000000000000000000000) else if j = 3 then (1748890503542549978988063 / 100000000000000000000000) else if j = 4 then (1288969431526265552179211 / 50000000000000000000000) else if j = 5 then (1284044069681724842268977 / 50000000000000000000000) else if j = 6 then (1093704169844487594787097 / 25000000000000000000000) else if j = 7 then (2319372639612149100685201 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26442155033863206344232833 / 1000000000000000000000000000000) else if j = 0 then (11806826631393013903359027 / 250000000000000000000000000000) else if j = 1 then (84805623573779680087366159 / 1000000000000000000000000000000) else if j = 2 then (136540759743062848971401673 / 1000000000000000000000000000000) else if j = 3 then (88313214851099538982860909 / 500000000000000000000000000000) else if j = 4 then (182513977358939047231245879 / 1000000000000000000000000000000) else if j = 5 then (182513977358939047231245879 / 1000000000000000000000000000000) else if j = 6 then (182513977358939047231245879 / 1000000000000000000000000000000) else if j = 7 then (38256373409261383625465707 / 250000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell096
