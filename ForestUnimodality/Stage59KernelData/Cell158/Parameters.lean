import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell158
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (287083780734784549866414279801 / 1000000000000000000000000000000)
  probabilityCap := (2326 / 4431)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1549 / 1405)
def activityUpper : ℚ := (2326 / 2105)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (461101250780300137211043 / 200000000000000000000000)
  B := (1693591527336529845015889 / 1000000000000000000000000000)
  C := (1852929984983360811590103 / 5000000000000000000000000)
  dδ := (1705754679557068276274379 / 10000000000000000000000000)
  dM := (107447066771179625837597 / 62500000000000000000000000)
  wL := (3223132539493 / 2500000000000)
  wR := (3388433730253 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(6332947108393843116402877 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (23162610436093348198483 / 800000000000000000000) else if j = 0 then (3027617887589310541329723 / 100000000000000000000000) else if j = 1 then (5553828121103067161357103 / 100000000000000000000000) else if j = 2 then (926617665882991872194907 / 10000000000000000000000) else if j = 3 then (1018433500442333041746679 / 10000000000000000000000) else if j = 4 then (114027290722190061122987 / 62500000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13756454082625736077574819 / 500000000000000000000000000000) else if j = 0 then (22143617641730643632568693 / 500000000000000000000000000000) else if j = 1 then (9188830712311511978450909 / 125000000000000000000000000000) else if j = 2 then (27719244266861181878244717 / 250000000000000000000000000000) else if j = 3 then (521779617790305239620407 / 4000000000000000000000000000) else if j = 4 then (521779617790305239620407 / 4000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1549 / 2954)
  hi := (2326 / 4431)
  vmin := (4896230 / 19633761)
  damping := (4896230 / 19633761)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell158
