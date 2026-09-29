import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell061
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (273644310281882930594772493241 / 1000000000000000000000000000000)
  probabilityCap := (9287 / 19012)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4631 / 4875)
def activityUpper : ℚ := (9287 / 9725)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (31)
  A := (808187119000628708093359 / 250000000000000000000000)
  B := (-7641062104757063988547117 / 100000000000000000000000000)
  C := (-78108421587371021539703 / 781250000000000000000000)
  dδ := (1271392350873625787244237 / 10000000000000000000000000)
  dM := (0)
  wL := (5511955450723 / 2500000000000)
  wR := (1122011137319 / 625000000000)
  wC := (1 / 10000000000000)
  price := ![(7725459218877839262518137 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1201012028710424672794943 / 50000000000000000000000) else if j = 0 then (516205655083371084401733 / 50000000000000000000000) else if j = 1 then (573339795951399935347581 / 20000000000000000000000) else if j = 2 then (2356308370210497926677817 / 100000000000000000000000) else if j = 3 then (308387520003865027717893 / 20000000000000000000000) else if j = 4 then (2181940274213566510752571 / 100000000000000000000000) else if j = 5 then (2216530736454285133163467 / 100000000000000000000000) else if j = 6 then (217526530700559455056009 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (1621610118879498063664607 / 62500000000000000000000000000) else if j = 0 then (6147333001971464551213789 / 125000000000000000000000000000) else if j = 1 then (17952707757744379548772549 / 200000000000000000000000000000) else if j = 2 then (29447047320550135515238877 / 200000000000000000000000000000) else if j = 3 then (99929748391172377968049661 / 500000000000000000000000000000) else if j = 4 then (108667424620901372244745093 / 500000000000000000000000000000) else if j = 5 then (108667424620901372244745093 / 500000000000000000000000000000) else if j = 6 then (108667424620901372244745093 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (4631 / 9506)
  hi := (9287 / 19012)
  vmin := (22576125 / 90364036)
  damping := (22576125 / 90364036)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell061
