import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell048
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (135598780773301553703491654279 / 500000000000000000000000000000)
  probabilityCap := (4487 / 9312)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 18), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 19), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21), (77, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (2983 / 3225)
def activityUpper : ℚ := (4487 / 4825)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (1582227881619724233431157 / 500000000000000000000000)
  B := (-7389558924199879363925447 / 100000000000000000000000000)
  C := (-8334281866311984976469773 / 100000000000000000000000000)
  dδ := (1304794656186534507202879 / 10000000000000000000000000)
  dM := (1017559177012520167226323 / 10000000000000000000000000000)
  wL := (5511670086489 / 2500000000000)
  wR := (448832991351 / 250000000000)
  wC := (1 / 10000000000000)
  price := ![(862244630140149181940501 / 125000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (558345209594850899748053 / 25000000000000000000000) else if j = 0 then (1374229084603907402595269 / 100000000000000000000000) else if j = 1 then (2579770248020120249066167 / 100000000000000000000000) else if j = 2 then (1038581345773163100432157 / 50000000000000000000000) else if j = 3 then (1333271697614532413922461 / 100000000000000000000000) else if j = 4 then (972669590391238614301983 / 50000000000000000000000) else if j = 5 then (1164398640105095417141001 / 50000000000000000000000) else if j = 6 then (495552509241444028020851 / 25000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (63156317969921398387873 / 2500000000000000000000000000) else if j = 0 then (49171581401501904930766539 / 1000000000000000000000000000000) else if j = 1 then (46082337778034373954566823 / 500000000000000000000000000000) else if j = 2 then (153016677437818784200034257 / 1000000000000000000000000000000) else if j = 3 then (42352258441893643394968509 / 200000000000000000000000000000) else if j = 4 then (236471193212772556328518391 / 1000000000000000000000000000000) else if j = 5 then (236471193212772556328518391 / 1000000000000000000000000000000) else if j = 6 then (236471193212772556328518391 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (2983 / 6208)
  hi := (4487 / 9312)
  vmin := (9620175 / 38539264)
  damping := (9620175 / 38539264)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell048
