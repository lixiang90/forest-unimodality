import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell099
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (278772154011212467883159759871 / 1000000000000000000000000000000)
  probabilityCap := (203 / 404)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (405 / 403)
def activityUpper : ℚ := (203 / 201)

def row : RationalRow (Fin 0) where
  terms := Finset.univ
  scale := (24)
  A := (-357119577021336248390071 / 200000000000000000000000)
  B := (1156668353263347326365107 / 5000000000000000000000000)
  C := (8229591296075602913084879 / 100000000000000000000000000)
  dδ := (1213500981313337806488661 / 10000000000000000000000000)
  dM := (5534009021295107494387011 / 1000000000000000000000000000)
  wL := (0)
  wR := (752993076633 / 2500000000000)
  wC := (9247006923367 / 10000000000000)
  price := fun i => Fin.elim0 i
  retention := fun i => Fin.elim0 i
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2380899403532674440953087 / 100000000000000000000000) else if j = 0 then (37482104291639499749067 / 1250000000000000000000) else if j = 1 then (4831235422890455311062397 / 100000000000000000000000) else if j = 2 then (6642580058615368443497573 / 100000000000000000000000) else if j = 3 then (1591504532973650931637621 / 100000000000000000000000) else if j = 4 then (1041957173683943516095951 / 50000000000000000000000) else if j = 5 then (1095583206312944390958819 / 50000000000000000000000) else if j = 6 then (1532324444868696033950073 / 50000000000000000000000) else if j = 7 then (138886002882168870797841 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26116016463011584545536237 / 1000000000000000000000000000000) else if j = 0 then (46306282055269972784804567 / 1000000000000000000000000000000) else if j = 1 then (84491457148313223951554287 / 1000000000000000000000000000000) else if j = 2 then (27109728634825757717829793 / 200000000000000000000000000000) else if j = 3 then (174477145130048534277559727 / 1000000000000000000000000000000) else if j = 4 then (44850675758846788344274187 / 250000000000000000000000000000) else if j = 5 then (44850675758846788344274187 / 250000000000000000000000000000) else if j = 6 then (44850675758846788344274187 / 250000000000000000000000000000) else if j = 7 then (18709261774882927513344261 / 125000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (405 / 808)
  hi := (203 / 404)
  vmin := (40803 / 163216)
  damping := (40803 / 163216)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell099
