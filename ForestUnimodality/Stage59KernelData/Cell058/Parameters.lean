import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell058
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (68290524061286535331421838563 / 250000000000000000000000000000)
  probabilityCap := (4631 / 9506)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9237 / 9775)
def activityUpper : ℚ := (4631 / 4875)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (735912529196083444155363 / 250000000000000000000000)
  B := (-3406948853996483866923839 / 50000000000000000000000000)
  C := (-224477490922333794420851 / 2000000000000000000000000)
  dδ := (1287833981456547038924043 / 10000000000000000000000000)
  dM := (0)
  wL := (1390652195649 / 625000000000)
  wR := (4437391217403 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(3216640119026823896319911 / 500000000000000000000000), (941153633748682771908989 / 500000000000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (229018718652135220281707 / 10000000000000000000000) else if j = 0 then (330613437700586443313 / 50000000000000000000) else if j = 1 then (1399498674345557702736187 / 50000000000000000000000) else if j = 2 then (223450679054350231922399 / 10000000000000000000000) else if j = 3 then (338975026854473338033813 / 25000000000000000000000) else if j = 4 then (377785472680565419523191 / 20000000000000000000000) else if j = 5 then (961609130556464464234523 / 50000000000000000000000) else if j = 6 then (5700729682056112856969321 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (12903780412665722427122457 / 500000000000000000000000000000) else if j = 0 then (12293709344593880029339001 / 250000000000000000000000000000) else if j = 1 then (9023018463655727014323689 / 100000000000000000000000000000) else if j = 2 then (74178466022402340207894967 / 500000000000000000000000000000) else if j = 3 then (202155617680410974632568983 / 1000000000000000000000000000000) else if j = 4 then (110495877187117313655515059 / 500000000000000000000000000000) else if j = 5 then (110495877187117313655515059 / 500000000000000000000000000000) else if j = 6 then (110495877187117313655515059 / 500000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell058
