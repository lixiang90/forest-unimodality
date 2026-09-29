import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell069
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (137539039664402802851605377441 / 500000000000000000000000000000)
  probabilityCap := (4777 / 9702)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9529 / 9875)
def activityUpper : ℚ := (4777 / 4925)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (1558428504769638748228999 / 500000000000000000000000)
  B := (-7965861958953525390203509 / 100000000000000000000000000)
  C := (-2633452112383162166397987 / 100000000000000000000000000)
  dδ := (1312531598589437298318927 / 10000000000000000000000000)
  dM := (7586589923998907796821867 / 100000000000000000000000000000)
  wL := (5180266959217 / 2500000000000)
  wR := (2409866520391 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(6469478478982022551235787 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1053541921568173300727267 / 50000000000000000000000) else if j = 0 then (315694929440118201569021 / 20000000000000000000000) else if j = 1 then (43992024977612317115927 / 2000000000000000000000) else if j = 2 then (928372137639617278637161 / 50000000000000000000000) else if j = 3 then (255878458464610787359561 / 20000000000000000000000) else if j = 4 then (881738972567740653119017 / 50000000000000000000000) else if j = 5 then (42892116052766464662227 / 2500000000000000000000) else if j = 6 then (774169181365112546444607 / 50000000000000000000000) else if j = 7 then (872016243287022518870799 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25530861305273956186250903 / 1000000000000000000000000000000) else if j = 0 then (47245752144860191667238547 / 1000000000000000000000000000000) else if j = 1 then (43521986777143632425845031 / 500000000000000000000000000000) else if j = 2 then (143787402478813570867700419 / 1000000000000000000000000000000) else if j = 3 then (192714851239397924948807187 / 1000000000000000000000000000000) else if j = 4 then (103163625962379587567300187 / 500000000000000000000000000000) else if j = 5 then (103163625962379587567300187 / 500000000000000000000000000000) else if j = 6 then (103163625962379587567300187 / 500000000000000000000000000000) else if j = 7 then (179235992160310870986651941 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9529 / 19404)
  hi := (4777 / 9702)
  vmin := (94098875 / 376515216)
  damping := (94098875 / 376515216)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell069
