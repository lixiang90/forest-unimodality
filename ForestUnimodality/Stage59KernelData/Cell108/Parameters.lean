import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell108
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (280115638765263004850299439077 / 1000000000000000000000000000000)
  probabilityCap := (10429 / 20604)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (51 / 50)
def activityUpper : ℚ := (10429 / 10175)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (3816029984434951704557193 / 5000000000000000000000000)
  B := (21480949307545532667163 / 400000000000000000000000)
  C := (79755922125874568508197 / 1562500000000000000000000)
  dδ := (52660844420507524343833 / 400000000000000000000000)
  dM := (65359163550962373666689 / 31250000000000000000000000)
  wL := (622811443 / 1220703125)
  wR := (1722663232151 / 2500000000000)
  wC := (1400363786517 / 2000000000000)
  price := ![(1563771116742567190982527 / 1000000000000000000000000), (797037763530300757963687 / 250000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2394377870973714550473233 / 100000000000000000000000) else if j = 0 then (1066264905687725139671329 / 50000000000000000000000) else if j = 1 then (2247198421546063329401477 / 100000000000000000000000) else if j = 2 then (95123886272528501706347 / 3125000000000000000000) else if j = 3 then (1442122980308248969549823 / 100000000000000000000000) else if j = 4 then (1587628663617609170444211 / 100000000000000000000000) else if j = 5 then (1313278594964406309486549 / 100000000000000000000000) else if j = 6 then (1696471044263548222374993 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13268968338827065903070693 / 500000000000000000000000000000) else if j = 0 then (46365170746553644604447747 / 1000000000000000000000000000000) else if j = 1 then (8335976501360233012292543 / 100000000000000000000000000000) else if j = 2 then (5292739252555824516675037 / 40000000000000000000000000000) else if j = 3 then (167824595989985062792019973 / 1000000000000000000000000000000) else if j = 4 then (6801391406115881952770409 / 40000000000000000000000000000) else if j = 5 then (6801391406115881952770409 / 40000000000000000000000000000) else if j = 6 then (6801391406115881952770409 / 40000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (51 / 101)
  hi := (10429 / 20604)
  vmin := (106115075 / 424524816)
  damping := (106115075 / 424524816)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell108
