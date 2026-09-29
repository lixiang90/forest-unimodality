import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell082
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (276487894771556723313577579743 / 1000000000000000000000000000000)
  probabilityCap := (131 / 264)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 18), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 20), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (49 / 50)
def activityUpper : ℚ := (131 / 133)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (1361637093898917142354321 / 500000000000000000000000)
  B := (-1268922847792427754942679 / 20000000000000000000000000)
  C := (-1955054871644779264372449 / 500000000000000000000000000)
  dδ := (1219360319680824061849833 / 10000000000000000000000000)
  dM := (0)
  wL := (848119292833 / 625000000000)
  wR := (827979452797 / 625000000000)
  wC := (82390125437 / 250000000000)
  price := ![(5771756101988185783113749 / 1000000000000000000000000), (874331100300676289371893 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1302125499058873892010979 / 50000000000000000000000) else if j = 0 then (1753335632724451542685529 / 100000000000000000000000) else if j = 1 then (654185028380723210261749 / 25000000000000000000000) else if j = 2 then (441392019956112591216879 / 20000000000000000000000) else if j = 3 then (187291913890112371454677 / 12500000000000000000000) else if j = 4 then (1777827173456622844582853 / 100000000000000000000000) else if j = 5 then (1162835428099070922414171 / 125000000000000000000000) else if j = 6 then (1194281277689159637134253 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6484356179062903670554963 / 250000000000000000000000000000) else if j = 0 then (23633253343765428492153549 / 500000000000000000000000000000) else if j = 1 then (86118843237052330970323717 / 1000000000000000000000000000000) else if j = 2 then (17585676145267829834839689 / 125000000000000000000000000000) else if j = 3 then (1485466091244852655117573 / 8000000000000000000000000000) else if j = 4 then (48942204323806021400902861 / 250000000000000000000000000000) else if j = 5 then (48942204323806021400902861 / 250000000000000000000000000000) else if j = 6 then (48942204323806021400902861 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (131 / 264)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell082
