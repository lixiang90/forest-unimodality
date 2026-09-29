import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell146
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (285864675346841191102524153151 / 1000000000000000000000000000000)
  probabilityCap := (109 / 209)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (22647 / 20825)
def activityUpper : ℚ := (109 / 100)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (2724317288473611460176471 / 1000000000000000000000000)
  B := (-4139484601481778491827157 / 100000000000000000000000000)
  C := (40925940731661647475903 / 200000000000000000000000)
  dδ := (369883250019390069640579 / 2500000000000000000000000)
  dM := (1038884857714693062211847 / 1250000000000000000000000000)
  wL := (987852036869 / 625000000000)
  wR := (6048591852523 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1332309904135219014165159 / 200000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (1292230883048640777133187 / 50000000000000000000000) else if j = 0 then (31509716896790536111439 / 1250000000000000000000) else if j = 1 then (3994038389685997003653029 / 100000000000000000000000) else if j = 2 then (5660828284069861382477029 / 100000000000000000000000) else if j = 3 then (6545154452402374545272323 / 100000000000000000000000) else if j = 4 then (4262119950474757779090851 / 1000000000000000000000000) else if j = 5 then (337912223292481495029449 / 125000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (27138085702238212977361379 / 1000000000000000000000000000000) else if j = 0 then (22142282999403527625861809 / 500000000000000000000000000000) else if j = 1 then (74516967562521908862176023 / 1000000000000000000000000000000) else if j = 2 then (56970158686943355399217143 / 500000000000000000000000000000) else if j = 3 then (135892121638580480768774837 / 1000000000000000000000000000000) else if j = 4 then (135892121638580480768774837 / 1000000000000000000000000000000) else if j = 5 then (135892121638580480768774837 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (22647 / 43472)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell146
