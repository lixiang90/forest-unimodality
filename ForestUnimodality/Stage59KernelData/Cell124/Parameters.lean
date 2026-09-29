import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell124
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (141788221398418281696138323771 / 500000000000000000000000000000)
  probabilityCap := (21967 / 42642)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (53 / 50)
def activityUpper : ℚ := (21967 / 20675)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (-263507793537646922499107 / 200000000000000000000000)
  B := (488554122212726399387961 / 2500000000000000000000000)
  C := (1747700679901361964230233 / 20000000000000000000000000)
  dδ := (79338971121113380929879 / 625000000000000000000000)
  dM := (1161839102417206240347447 / 250000000000000000000000000)
  wL := (4489448028267 / 2500000000000)
  wR := (1377637992933 / 625000000000)
  wC := (1 / 10000000000000)
  price := ![(56843800686987033810027 / 50000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2515152101234539472329743 / 100000000000000000000000) else if j = 0 then (3142322957458612719960911 / 100000000000000000000000) else if j = 1 then (4936559295737516350754959 / 100000000000000000000000) else if j = 2 then (3046264005360980675618521 / 50000000000000000000000) else if j = 3 then (1831194545383696947737917 / 100000000000000000000000) else if j = 4 then (2179894271972191432951149 / 100000000000000000000000) else if j = 5 then (546570198114219891749599 / 20000000000000000000000) else if j = 6 then (349494811177340309882311 / 10000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26363710432460182941130389 / 1000000000000000000000000000000) else if j = 0 then (22067390819672454364552827 / 500000000000000000000000000000) else if j = 1 then (7618772905939517004218627 / 100000000000000000000000000000) else if j = 2 then (59755591656537652714761579 / 500000000000000000000000000000) else if j = 3 then (146226695930130719792507337 / 1000000000000000000000000000000) else if j = 4 then (146226695930130719792507337 / 1000000000000000000000000000000) else if j = 5 then (146226695930130719792507337 / 1000000000000000000000000000000) else if j = 6 then (146226695930130719792507337 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (21967 / 42642)
  vmin := (454167725 / 1818340164)
  damping := (454167725 / 1818340164)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell124
