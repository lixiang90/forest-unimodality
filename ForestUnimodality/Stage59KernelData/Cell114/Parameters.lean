import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell114
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (28142908423659405362883567679 / 100000000000000000000000000000)
  probabilityCap := (26 / 51)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (3493 / 3375)
def activityUpper : ℚ := (26 / 25)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (439630934558864467010153 / 200000000000000000000000)
  B := (-2241558659004993375729597 / 100000000000000000000000000)
  C := (1003466140580960841433011 / 10000000000000000000000000)
  dδ := (668432394114913952520851 / 5000000000000000000000000)
  dM := (476851635735520032292889 / 500000000000000000000000000)
  wL := (2248581016473 / 1250000000000)
  wR := (5502837967053 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(2809358568508294240473333 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2555018760642076003364309 / 100000000000000000000000) else if j = 0 then (2698627338678400278126901 / 100000000000000000000000) else if j = 1 then (474455185303753168568619 / 12500000000000000000000) else if j = 2 then (4580737602522659557280349 / 100000000000000000000000) else if j = 3 then (1551511314010745934410807 / 100000000000000000000000) else if j = 4 then (779290748376977671085797 / 50000000000000000000000) else if j = 5 then (25376016616948843251933 / 1562500000000000000000) else if j = 6 then (155544642444809095849223 / 10000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (5394653799440858696396359 / 200000000000000000000000000000) else if j = 0 then (2322219182010994161403623 / 50000000000000000000000000000) else if j = 1 then (20573716018928654274101481 / 250000000000000000000000000000) else if j = 2 then (64631619413438389961776153 / 500000000000000000000000000000) else if j = 3 then (80789524266797987452220191 / 500000000000000000000000000000) else if j = 4 then (80789524266797987452220191 / 500000000000000000000000000000) else if j = 5 then (80789524266797987452220191 / 500000000000000000000000000000) else if j = 6 then (80789524266797987452220191 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (3493 / 6868)
  hi := (26 / 51)
  vmin := (650 / 2601)
  damping := (650 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell114
