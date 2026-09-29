import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell057
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (68290524061286535331421838563 / 250000000000000000000000000000)
  probabilityCap := (4631 / 9506)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 17), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19), (69, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9237 / 9775)
def activityUpper : ℚ := (4631 / 4875)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (25)
  A := (662919997821619179617869 / 250000000000000000000000)
  B := (-5341146161665712155386387 / 100000000000000000000000000)
  C := (-6007093678906366696068631 / 100000000000000000000000000)
  dδ := (156159795394600240889 / 1220703125000000000000)
  dM := (4213110648677171059424407 / 10000000000000000000000000000)
  wL := (671460242981 / 312500000000)
  wR := (4628318056151 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(5701462279710511005248463 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2067881262817894238992267 / 100000000000000000000000) else if j = 0 then (813887021565974144721167 / 50000000000000000000000) else if j = 1 then (2293122975157078613506201 / 100000000000000000000000) else if j = 2 then (382852057508302152655233 / 20000000000000000000000) else if j = 3 then (658363774846650962047079 / 50000000000000000000000) else if j = 4 then (1982704495946907030656803 / 100000000000000000000000) else if j = 5 then (316037001003283624100959 / 12500000000000000000000) else if j = 6 then (507275791826311177601383 / 20000000000000000000000) else if j = 7 then (1237875181803910429323423 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (12903780412665722427122457 / 500000000000000000000000000000) else if j = 0 then (12293709344593880029339001 / 250000000000000000000000000000) else if j = 1 then (9023018463655727014323689 / 100000000000000000000000000000) else if j = 2 then (74178466022402340207894967 / 500000000000000000000000000000) else if j = 3 then (202155617680410974632568983 / 1000000000000000000000000000000) else if j = 4 then (110495877187117313655515059 / 500000000000000000000000000000) else if j = 5 then (110495877187117313655515059 / 500000000000000000000000000000) else if j = 6 then (110495877187117313655515059 / 500000000000000000000000000000) else if j = 7 then (196016913062273240202611499 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9237 / 19012)
  hi := (4631 / 9506)
  vmin := (90291675 / 361456144)
  damping := (90291675 / 361456144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell057
