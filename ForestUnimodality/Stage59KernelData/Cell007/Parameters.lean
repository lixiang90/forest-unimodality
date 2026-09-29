import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell007
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (13 / 42)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (59, 18), (60, 15), (60, 16), (60, 17), (60, 18), (61, 16), (61, 17), (61, 18), (62, 16), (62, 17), (62, 18), (62, 19), (63, 16), (63, 17), (63, 18), (63, 19), (64, 16), (64, 17), (64, 18), (64, 19), (65, 17), (65, 18), (65, 19), (65, 20), (66, 17), (66, 18), (66, 19), (66, 20), (67, 17), (67, 18), (67, 19), (67, 20), (68, 17), (68, 18), (68, 19), (68, 20), (68, 21), (69, 18), (69, 19), (69, 20), (69, 21), (70, 18), (70, 19), (70, 20), (70, 21), (71, 18), (71, 19), (71, 20), (71, 21), (72, 18), (72, 19), (72, 20), (72, 21), (72, 22), (73, 19), (73, 20), (73, 21), (73, 22), (74, 19), (74, 20), (74, 21), (74, 22), (75, 19), (75, 20), (75, 21), (75, 22), (75, 23), (76, 19), (76, 20), (76, 21), (76, 22), (76, 23), (77, 20), (77, 21), (77, 22), (77, 23), (78, 20), (78, 21), (78, 22), (78, 23), (78, 24), (79, 20), (79, 21), (79, 22), (79, 23), (79, 24)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (19 / 44)
def activityUpper : ℚ := (13 / 29)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (45)
  A := (9858406622865543432752133 / 10000000000000000000000000)
  B := (4039174375628082347411407 / 100000000000000000000000000)
  C := (-9015998002698162594459319 / 100000000000000000000000000)
  dδ := (5417745153492646570381197 / 100000000000000000000000000)
  dM := (2356387030951293139581851 / 50000000000000000000000000000)
  wL := (4)
  wR := (0)
  wC := (0)
  price := ![(689248439938581203279 / 100000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := {1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = 1 then (4966330554562455290579237 / 100000000000000000000000) else if j = 2 then (172784931186663257562941 / 10000000000000000000000) else if j = 3 then (210006686541816378621661 / 20000000000000000000000) else if j = 4 then (7036091593163133595112413 / 1000000000000000000000000) else if j = 5 then (3838079256664622906924933 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (355004202457629364112661159 / 1000000000000000000000000000000) else if j = 2 then (395966225818125059971814369 / 500000000000000000000000000000) else if j = 3 then (89711098036918958899864193 / 62500000000000000000000000000) else if j = 4 then (426932815273132276200379339 / 200000000000000000000000000000) else if j = 5 then (1309534308385857654883855857 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (19 / 63)
  hi := (13 / 42)
  vmin := (836 / 3969)
  damping := (33440000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell007
