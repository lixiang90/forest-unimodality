import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell103
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (279220410815494811999635067933 / 1000000000000000000000000000000)
  probabilityCap := (407 / 808)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (203 / 201)
def activityUpper : ℚ := (407 / 401)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (381760240715500259458537 / 2500000000000000000000000)
  B := (195642028359122380209989 / 2500000000000000000000000)
  C := (1067738622416622949751197 / 50000000000000000000000000)
  dδ := (312351870839332884655093 / 2500000000000000000000000)
  dM := (217152403306815344752323 / 100000000000000000000000000)
  wL := (1130863654483 / 2500000000000)
  wR := (658274604239 / 1250000000000)
  wC := (7552587137039 / 10000000000000)
  price := ![(4051794583861467735630413 / 1000000000000000000000000), (340197551901235295535031 / 250000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (627794400599664825790569 / 25000000000000000000000) else if j = 0 then (1804874186686594939033057 / 100000000000000000000000) else if j = 1 then (1206493134062808358919483 / 50000000000000000000000) else if j = 2 then (1038822499915702657347083 / 50000000000000000000000) else if j = 3 then (1438469863501063628064003 / 100000000000000000000000) else if j = 4 then (311162402485188067657873 / 20000000000000000000000) else if j = 5 then (517144972367751343256259 / 50000000000000000000000) else if j = 6 then (1432420506699961038066249 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26274682670896360713098329 / 1000000000000000000000000000000) else if j = 0 then (11589385555779597809292721 / 250000000000000000000000000000) else if j = 1 then (84167268613821006915011011 / 1000000000000000000000000000000) else if j = 2 then (134546134638844795284003983 / 1000000000000000000000000000000) else if j = 3 then (172331449600073198480469967 / 1000000000000000000000000000000) else if j = 4 then (176321357476846769981860549 / 1000000000000000000000000000000) else if j = 5 then (176321357476846769981860549 / 1000000000000000000000000000000) else if j = 6 then (176321357476846769981860549 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (203 / 404)
  hi := (407 / 808)
  vmin := (163207 / 652864)
  damping := (163207 / 652864)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell103
