import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell011
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (29 / 85)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 15), (60, 16), (60, 17), (60, 18), (60, 19), (60, 20), (61, 16), (61, 17), (61, 18), (61, 19), (61, 20), (62, 16), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 16), (63, 17), (63, 18), (63, 19), (63, 20), (63, 21), (64, 16), (64, 17), (64, 18), (64, 19), (64, 20), (64, 21), (65, 17), (65, 18), (65, 19), (65, 20), (65, 21), (65, 22), (66, 17), (66, 18), (66, 19), (66, 20), (66, 21), (66, 22), (67, 17), (67, 18), (67, 19), (67, 20), (67, 21), (67, 22), (68, 17), (68, 18), (68, 19), (68, 20), (68, 21), (68, 22), (68, 23), (69, 18), (69, 19), (69, 20), (69, 21), (69, 22), (69, 23), (70, 18), (70, 19), (70, 20), (70, 21), (70, 22), (70, 23), (71, 18), (71, 19), (71, 20), (71, 21), (71, 22), (71, 23), (71, 24), (72, 18), (72, 19), (72, 20), (72, 21), (72, 22), (72, 23), (72, 24), (73, 19), (73, 20), (73, 21), (73, 22), (73, 23), (73, 24), (74, 19), (74, 20), (74, 21), (74, 22), (74, 23), (74, 24), (75, 19), (75, 20), (75, 21), (75, 22), (75, 23), (75, 24), (76, 19), (76, 20), (76, 21), (76, 22), (76, 23), (76, 24), (77, 20), (77, 21), (77, 22), (77, 23), (77, 24), (78, 20), (78, 21), (78, 22), (78, 23), (78, 24), (79, 20), (79, 21), (79, 22), (79, 23), (79, 24)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1 / 2)
def activityUpper : ℚ := (29 / 56)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (42)
  A := (-352102547512842609000927 / 100000000000000000000000)
  B := (3740495156148670452544991 / 10000000000000000000000000)
  C := (-808754521404471404810721 / 5000000000000000000000000)
  dδ := (1095353647763200322096111 / 12500000000000000000000000)
  dM := (2870082693317484948819507 / 500000000000000000000000000)
  wL := (281845963543 / 78125000000)
  wR := (980929166623 / 2500000000000)
  wC := (1 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (7539504803517917075339483 / 1000000000000000000000000) else if j = 1 then (4792478821136829481019959 / 100000000000000000000000) else if j = 2 then (2121993731628385404519577 / 100000000000000000000000) else if j = 3 then (3158532692853468354377 / 195312500000000000000) else if j = 4 then (137006687816234897780987 / 10000000000000000000000) else if j = 5 then (9566517055493815036015803 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (58782731881717860436165567 / 1000000000000000000000000000000) else if j = 1 then (438389172844392890196944629 / 1000000000000000000000000000000) else if j = 2 then (169308921926110357593302753 / 200000000000000000000000000000) else if j = 3 then (166024912664612527381363691 / 125000000000000000000000000000) else if j = 4 then (170986576721256120153680307 / 100000000000000000000000000000) else if j = 5 then (1860521852903555664558528187 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1 / 3)
  hi := (29 / 85)
  vmin := (2 / 9)
  damping := (80000000000000000000000000000000000000000 / 888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell011
