import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell086
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (55389495937292011283385574343 / 200000000000000000000000000000)
  probabilityCap := (197 / 396)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 20), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (131 / 133)
def activityUpper : ℚ := (197 / 199)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (2898994363920947365699021 / 1000000000000000000000000)
  B := (-6798259218937016679085161 / 100000000000000000000000000)
  C := (307022360856572598675207 / 20000000000000000000000000)
  dδ := (604104245603003520148633 / 5000000000000000000000000)
  dM := (0)
  wL := (1954007986393 / 2500000000000)
  wR := (16545608941 / 20000000000)
  wC := (2988895447991 / 5000000000000)
  price := ![(3560827598676034710933891 / 500000000000000000000000), (1933443054832934340780959 / 50000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2705364082489590416003011 / 100000000000000000000000) else if j = 0 then (218843353608464781245857 / 10000000000000000000000) else if j = 1 then (327725209486371937828153 / 12500000000000000000000) else if j = 2 then (1129350602979571682737969 / 50000000000000000000000) else if j = 3 then (1613426639044169874637191 / 100000000000000000000000) else if j = 4 then (1942469497328471561559127 / 100000000000000000000000) else if j = 5 then (130630350449890357822369 / 10000000000000000000000) else if j = 6 then (1696065003129446679963621 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13039972610887615958385679 / 500000000000000000000000000000) else if j = 0 then (23643394944624508322701637 / 500000000000000000000000000000) else if j = 1 then (17168163099359313627652723 / 200000000000000000000000000000) else if j = 2 then (17464816985341116974010203 / 125000000000000000000000000000) else if j = 3 then (183478097628740993347266579 / 1000000000000000000000000000000) else if j = 4 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 5 then (192469312487158406336365351 / 1000000000000000000000000000000) else if j = 6 then (192469312487158406336365351 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell086
