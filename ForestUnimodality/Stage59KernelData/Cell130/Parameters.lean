import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell130
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (142103513213412700830147483707 / 500000000000000000000000000000)
  probabilityCap := (107 / 207)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (7339 / 6875)
def activityUpper : ℚ := (107 / 100)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1153917258280168798307841 / 20000000000000000000000000)
  B := (70883488971670398359759 / 625000000000000000000000)
  C := (831320747063804127430231 / 10000000000000000000000000)
  dδ := (129630112551885973148913 / 1000000000000000000000000)
  dM := (330579496420086663827087 / 100000000000000000000000000)
  wL := (4498795881857 / 2500000000000)
  wR := (2750602059071 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(838914169095740476223 / 320000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1244788508436928786693443 / 50000000000000000000000) else if j = 0 then (3015394405564471114189473 / 100000000000000000000000) else if j = 1 then (2336532977156548085417853 / 50000000000000000000000) else if j = 2 then (2839727221430906922705617 / 50000000000000000000000) else if j = 3 then (367485466151644217802641 / 20000000000000000000000) else if j = 4 then (268619984977620962496303 / 12500000000000000000000) else if j = 5 then (677063389463582687710641 / 25000000000000000000000) else if j = 6 then (3451721043951627621027001 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26589536195297122677690637 / 1000000000000000000000000000000) else if j = 0 then (44200447405964188510109239 / 1000000000000000000000000000000) else if j = 1 then (75765617294883430084013021 / 1000000000000000000000000000000) else if j = 2 then (59007490105049400376957181 / 500000000000000000000000000000) else if j = 3 then (35845671559142159107497353 / 250000000000000000000000000000) else if j = 4 then (35845671559142159107497353 / 250000000000000000000000000000) else if j = 5 then (35845671559142159107497353 / 250000000000000000000000000000) else if j = 6 then (35845671559142159107497353 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (7339 / 14214)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell130
