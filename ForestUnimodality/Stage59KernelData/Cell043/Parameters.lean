import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell043
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (269689702260771572442712612683 / 1000000000000000000000000000000)
  probabilityCap := (581 / 1216)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 20), (72, 20), (73, 20), (74, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (869 / 955)
def activityUpper : ℚ := (581 / 635)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (27)
  A := (-179855085878302819912733 / 100000000000000000000000)
  B := (1159075129285982996840687 / 5000000000000000000000000)
  C := (-1369841462690982725192157 / 10000000000000000000000000)
  dδ := (33336960755980658832609 / 250000000000000000000000)
  dM := (2604815675049027001719537 / 500000000000000000000000000)
  wL := (1159025274977 / 500000000000)
  wR := (2102436812557 / 1250000000000)
  wC := (1 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1099099348797289543711031 / 50000000000000000000000) else if j = 0 then (2328053671506251731671 / 100000000000000000000) else if j = 1 then (556702280425558839738187 / 20000000000000000000000) else if j = 2 then (291999647470475176547211 / 12500000000000000000000) else if j = 3 then (269629601497880910798699 / 12500000000000000000000) else if j = 4 then (2900478631498840442759501 / 100000000000000000000000) else if j = 5 then (4538172913864143254158989 / 100000000000000000000000) else if j = 6 then (3195080536631011725035023 / 50000000000000000000000) else if j = 7 then (1658014599761261465005191 / 25000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (1055959123748306541232751 / 25000000000000000000000000000) else if j = 0 then (16934171942734223291986481 / 200000000000000000000000000000) else if j = 1 then (1204953652067671555688313 / 7812500000000000000000000000) else if j = 2 then (219139798093078222478915499 / 1000000000000000000000000000000) else if j = 3 then (49743834745211520248921041 / 200000000000000000000000000000) else if j = 4 then (49743834745211520248921041 / 200000000000000000000000000000) else if j = 5 then (49743834745211520248921041 / 200000000000000000000000000000) else if j = 6 then (49743834745211520248921041 / 200000000000000000000000000000) else if j = 7 then (49743834745211520248921041 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (869 / 1824)
  hi := (581 / 1216)
  vmin := (829895 / 3326976)
  damping := (829895 / 3326976)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell043
