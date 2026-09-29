import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell027
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (52106936406376832816242535427 / 200000000000000000000000000000)
  probabilityCap := (17 / 37)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 16), (60, 17), (60, 18), (60, 19), (60, 20), (61, 16), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 17), (64, 18), (64, 19), (64, 20), (65, 17), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 18), (67, 19), (67, 20), (68, 18), (68, 19), (68, 20), (69, 18), (69, 19), (69, 20), (70, 19), (70, 20), (71, 19), (71, 20), (72, 19), (72, 20), (73, 20), (74, 20), (75, 20), (76, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (301 / 365)
def activityUpper : ℚ := (17 / 20)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (-1313647266612470636658827 / 1000000000000000000000000)
  B := (2321717665147685905058239 / 10000000000000000000000000)
  C := (-1832612847272021838751499 / 5000000000000000000000000)
  dδ := (1568411368655231730162569 / 10000000000000000000000000)
  dM := (532129227835208360591901 / 100000000000000000000000000)
  wL := (3545014217331 / 1250000000000)
  wR := (2909971565337 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1116189955233983122084851 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (27775082014196129875927 / 2000000000000000000000) else if j = 1 then (1555624047186895175798327 / 50000000000000000000000) else if j = 2 then (2260580005632155931039051 / 100000000000000000000000) else if j = 3 then (447921029708876048402999 / 20000000000000000000000) else if j = 4 then (50957916702225645622093 / 2000000000000000000000) else if j = 5 then (173706063477391436933317 / 6250000000000000000000) else if j = 6 then (1538841348175910006546019 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (65587529386145358041785823 / 1000000000000000000000000000000) else if j = 1 then (62232053814674895494787663 / 250000000000000000000000000000) else if j = 2 then (366070904792205267616398017 / 1000000000000000000000000000000) else if j = 3 then (111677833347026494328481037 / 250000000000000000000000000000) else if j = 4 then (111677833347026494328481037 / 250000000000000000000000000000) else if j = 5 then (111677833347026494328481037 / 250000000000000000000000000000) else if j = 6 then (111677833347026494328481037 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (301 / 666)
  hi := (17 / 37)
  vmin := (109865 / 443556)
  damping := (109865 / 443556)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell027
