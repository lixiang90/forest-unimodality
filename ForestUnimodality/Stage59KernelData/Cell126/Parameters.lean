import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell126
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (283786726151015803777334043179 / 1000000000000000000000000000000)
  probabilityCap := (10996 / 21321)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (21967 / 20675)
def activityUpper : ℚ := (10996 / 10325)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (-148522963468971022138021 / 500000000000000000000000)
  B := (84687355037399766194417 / 625000000000000000000000)
  C := (1698452456160187418188201 / 20000000000000000000000000)
  dδ := (15985190785857271433823 / 125000000000000000000000)
  dM := (1839675261143293655621833 / 500000000000000000000000000)
  wL := (4497089603131 / 2500000000000)
  wR := (1375727599217 / 625000000000)
  wC := (1 / 10000000000000)
  price := ![(2143249582877871706187989 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1254751607008692282363427 / 50000000000000000000000) else if j = 0 then (3104163602784282005586647 / 100000000000000000000000) else if j = 1 then (2417734430687531244075217 / 50000000000000000000000) else if j = 2 then (738227198297451270292413 / 12500000000000000000000) else if j = 3 then (368657773377615356480419 / 20000000000000000000000) else if j = 4 then (546891947873906136834421 / 25000000000000000000000) else if j = 5 then (136942737625614086027781 / 5000000000000000000000) else if j = 6 then (10967784659482806564057 / 312500000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26439536806816285900837771 / 1000000000000000000000000000000) else if j = 0 then (1103948621352593291982029 / 25000000000000000000000000000) else if j = 1 then (38024495840447127743289669 / 500000000000000000000000000000) else if j = 2 then (232448944237663479161377 / 1953125000000000000000000000) else if j = 3 then (29055357010974526757190149 / 200000000000000000000000000000) else if j = 4 then (29055357010974526757190149 / 200000000000000000000000000000) else if j = 5 then (29055357010974526757190149 / 200000000000000000000000000000) else if j = 6 then (29055357010974526757190149 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (21967 / 42642)
  hi := (10996 / 21321)
  vmin := (113533700 / 454585041)
  damping := (113533700 / 454585041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell126
