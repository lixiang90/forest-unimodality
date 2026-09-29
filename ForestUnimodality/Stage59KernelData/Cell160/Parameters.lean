import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell160
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (143642379450060641160881088303 / 500000000000000000000000000000)
  probabilityCap := (4657 / 8862)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (2326 / 2105)
def activityUpper : ℚ := (4657 / 4205)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3318716603498555046570573 / 1000000000000000000000000)
  B := (-1391303178966265402527469 / 25000000000000000000000000)
  C := (516113691247557446195593 / 1250000000000000000000000)
  dδ := (452065755571319366490357 / 2500000000000000000000000)
  dM := (1679378669000474843392423 / 2000000000000000000000000000)
  wL := (192113408683 / 156250000000)
  wR := (6926185461071 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(3970060452056485722494017 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3}
  fixedPrice := fun j => if j = -1 then (1450235307276496499184759 / 50000000000000000000000) else if j = 0 then (264216415413043108628699 / 10000000000000000000000) else if j = 1 then (4421217285027077537051809 / 100000000000000000000000) else if j = 2 then (6130802536974530880797829 / 100000000000000000000000) else if j = 3 then (142327890261635054969247 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (27576261643567152124112389 / 1000000000000000000000000000000) else if j = 0 then (22144446963960823882397829 / 500000000000000000000000000000) else if j = 1 then (73347256632065119334580089 / 1000000000000000000000000000000) else if j = 2 then (862347715071156957944999 / 7812500000000000000000000000) else if j = 3 then (2024489492993978746234201 / 15625000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (2326 / 4431)
  hi := (4657 / 8862)
  vmin := (19582685 / 78535044)
  damping := (19582685 / 78535044)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell160
