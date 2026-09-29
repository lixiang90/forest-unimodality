import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell122
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (283149416963555229276955770059 / 1000000000000000000000000000000)
  probabilityCap := (53 / 103)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (10787 / 10225)
def activityUpper : ℚ := (53 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (1057613080766850525094469 / 500000000000000000000000)
  B := (-209239927067588621367733 / 10000000000000000000000000)
  C := (7478979985477191005927011 / 100000000000000000000000000)
  dδ := (1303158963362697209120711 / 10000000000000000000000000)
  dM := (587842886620951746634231 / 625000000000000000000000000)
  wL := (4553504891481 / 2500000000000)
  wR := (2723247554259 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(673753064386612088298989 / 125000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (9633743897934645872283 / 400000000000000000000) else if j = 0 then (632532550709960439405677 / 25000000000000000000000) else if j = 1 then (3576685435589394046473899 / 100000000000000000000000) else if j = 2 then (3901596279204711947841133 / 100000000000000000000000) else if j = 3 then (519465106923662006011 / 32000000000000000000) else if j = 4 then (1749151664894715452192031 / 100000000000000000000000) else if j = 5 then (397129386659398164738377 / 20000000000000000000000) else if j = 6 then (19295008157583759533793 / 781250000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13730922296303327871514153 / 500000000000000000000000000000) else if j = 0 then (11598365967831936343483149 / 250000000000000000000000000000) else if j = 1 then (4032680417051324924158249 / 50000000000000000000000000000) else if j = 2 then (124963628955932364904757587 / 1000000000000000000000000000000) else if j = 3 then (38314320198752847730232279 / 250000000000000000000000000000) else if j = 4 then (38314320198752847730232279 / 250000000000000000000000000000) else if j = 5 then (38314320198752847730232279 / 250000000000000000000000000000) else if j = 6 then (38314320198752847730232279 / 250000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (10787 / 21012)
  hi := (53 / 103)
  vmin := (2650 / 10609)
  damping := (2650 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell122
