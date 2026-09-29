import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell148
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (286070010697670776708336816587 / 1000000000000000000000000000000)
  probabilityCap := (4583 / 8778)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (109 / 100)
def activityUpper : ℚ := (4583 / 4195)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1607156156104866687684307 / 500000000000000000000000)
  B := (-1428471974502611985258227 / 20000000000000000000000000)
  C := (2153527709173828352806623 / 10000000000000000000000000)
  dδ := (47170876717332090033441 / 312500000000000000000000)
  dM := (3300728376711965068000809 / 10000000000000000000000000000)
  wL := (244353785513 / 156250000000)
  wR := (6090339431791 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1837325314459433478475603 / 250000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (1290235386831739816670961 / 50000000000000000000000) else if j = 0 then (2406455423836787943514537 / 100000000000000000000000) else if j = 1 then (3768786236543260059761451 / 100000000000000000000000) else if j = 2 then (5313927839048510293196159 / 100000000000000000000000) else if j = 3 then (6296725638922848133915977 / 100000000000000000000000) else if j = 4 then (1692101771213857075437659 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13597751585174898176482069 / 500000000000000000000000000000) else if j = 0 then (44277071377861054825613373 / 1000000000000000000000000000000) else if j = 1 then (9291809273709914245915979 / 125000000000000000000000000000) else if j = 2 then (113402108962726279035908159 / 1000000000000000000000000000000) else if j = 3 then (2108466074447099889272601 / 15625000000000000000000000000) else if j = 4 then (2108466074447099889272601 / 15625000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (109 / 209)
  hi := (4583 / 8778)
  vmin := (19225685 / 77053284)
  damping := (19225685 / 77053284)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell148
