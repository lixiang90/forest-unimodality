import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell136
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (71208195180923970514870119999 / 250000000000000000000000000000)
  probabilityCap := (22331 / 43056)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (11153 / 10375)
def activityUpper : ℚ := (22331 / 20725)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (541467984157879850459949 / 200000000000000000000000)
  B := (-5103772871710025860192417 / 100000000000000000000000000)
  C := (1079103943648976327018829 / 10000000000000000000000000)
  dδ := (85595579787681591588111 / 625000000000000000000000)
  dM := (2686064884241472195368361 / 5000000000000000000000000000)
  wL := (4381460009293 / 2500000000000)
  wR := (2809269995353 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(6422779302466613771116499 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (2420025501300315795560891 / 100000000000000000000000) else if j = 0 then (463654463652246064953033 / 20000000000000000000000) else if j = 1 then (806505478815959264693447 / 25000000000000000000000) else if j = 2 then (855575735933786241105281 / 25000000000000000000000) else if j = 3 then (1504254511167502528223849 / 100000000000000000000000) else if j = 4 then (230451355046117924985083 / 20000000000000000000000) else if j = 5 then (83644112889659572029899 / 6250000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26798026565716412160293267 / 1000000000000000000000000000000) else if j = 0 then (2211866272909138279239677 / 50000000000000000000000000000) else if j = 1 then (75301652691060577572147883 / 1000000000000000000000000000000) else if j = 2 then (58238426105049425693086027 / 500000000000000000000000000000) else if j = 3 then (28106019351310629201307067 / 200000000000000000000000000000) else if j = 4 then (28106019351310629201307067 / 200000000000000000000000000000) else if j = 5 then (28106019351310629201307067 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (11153 / 21528)
  hi := (22331 / 43056)
  vmin := (462809975 / 1853819136)
  damping := (462809975 / 1853819136)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell136
