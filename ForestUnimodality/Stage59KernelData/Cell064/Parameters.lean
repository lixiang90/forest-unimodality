import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell064
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (10965039727666275883725687439 / 40000000000000000000000000000)
  probabilityCap := (24 / 49)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (9287 / 9725)
def activityUpper : ℚ := (24 / 25)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (1454084317717822719629339 / 500000000000000000000000)
  B := (-3402633664828656062661949 / 50000000000000000000000000)
  C := (-2140746309076093853440703 / 50000000000000000000000000)
  dδ := (1256742109161200493527843 / 10000000000000000000000000)
  dM := (0)
  wL := (5263744870057 / 2500000000000)
  wR := (2368127564971 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(6501347783354813891776303 / 1000000000000000000000000), (1543253977411302324540543 / 1000000000000000000000000)]
  retention := ![(4 / 5), (3 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2482199862358670827688911 / 100000000000000000000000) else if j = 0 then (635033434120878866741 / 48828125000000000000) else if j = 1 then (666606801770449841626487 / 25000000000000000000000) else if j = 2 then (2164219237303663234683881 / 100000000000000000000000) else if j = 3 then (682748972918867558234979 / 50000000000000000000000) else if j = 4 then (1726936642020857703982983 / 100000000000000000000000) else if j = 5 then (284112649177086851182139 / 25000000000000000000000) else if j = 6 then (3598313646718569014382183 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26080600837363311916222579 / 1000000000000000000000000000000) else if j = 0 then (24587393815680436115595113 / 500000000000000000000000000000) else if j = 1 then (44642688283538359299062491 / 500000000000000000000000000000) else if j = 2 then (29219999316944179249893621 / 200000000000000000000000000000) else if j = 3 then (19756025458748306783501109 / 100000000000000000000000000000) else if j = 4 then (213707006164344664725372573 / 1000000000000000000000000000000) else if j = 5 then (213707006164344664725372573 / 1000000000000000000000000000000) else if j = 6 then (213707006164344664725372573 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (9287 / 19012)
  hi := (24 / 49)
  vmin := (90316075 / 361456144)
  damping := (90316075 / 361456144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell064
