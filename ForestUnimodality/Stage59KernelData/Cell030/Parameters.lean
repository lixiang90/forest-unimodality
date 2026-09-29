import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell030
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 16
  upperRank := 20
  density := (132491239559555667722491054517 / 500000000000000000000000000000)
  probabilityCap := (22 / 47)

def pairs : List (ℕ × ℕ) := [(59, 16), (59, 17), (59, 18), (59, 19), (59, 20), (60, 16), (60, 17), (60, 18), (60, 19), (60, 20), (61, 17), (61, 18), (61, 19), (61, 20), (62, 17), (62, 18), (62, 19), (62, 20), (63, 17), (63, 18), (63, 19), (63, 20), (64, 17), (64, 18), (64, 19), (64, 20), (65, 18), (65, 19), (65, 20), (66, 18), (66, 19), (66, 20), (67, 18), (67, 19), (67, 20), (68, 19), (68, 20), (69, 19), (69, 20), (70, 19), (70, 20), (71, 19), (71, 20), (72, 20), (73, 20), (74, 20), (75, 20)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (1613 / 1865)
def activityUpper : ℚ := (22 / 25)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (435647136491830724958163 / 100000000000000000000000)
  B := (-32909753456004642822863 / 312500000000000000000000)
  C := (-3631042852399755105352597 / 10000000000000000000000000)
  dδ := (214160127144912490471107 / 1250000000000000000000000)
  dM := (0)
  wL := (53204829761 / 19531250000)
  wR := (3189781790591 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(8334054326894309028261887 / 1000000000000000000000000), (6237014163789231790957501 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (703167320334463408215697 / 50000000000000000000000) else if j = 1 then (2929211075714748346854321 / 100000000000000000000000) else if j = 2 then (2127980471706107579166201 / 100000000000000000000000) else if j = 3 then (1858878007468579696137567 / 100000000000000000000000) else if j = 4 then (420231590425924217413467 / 25000000000000000000000) else if j = 5 then (265816296368741822320203 / 12500000000000000000000) else if j = 6 then (2263279677964597169648187 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (10367844630460524002744011 / 200000000000000000000000000000) else if j = 1 then (197372204026146743791563631 / 1000000000000000000000000000000) else if j = 2 then (70883045679293049128560601 / 250000000000000000000000000000) else if j = 3 then (66917560606325605820669099 / 200000000000000000000000000000) else if j = 4 then (66917560606325605820669099 / 200000000000000000000000000000) else if j = 5 then (66917560606325605820669099 / 200000000000000000000000000000) else if j = 6 then (66917560606325605820669099 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (1613 / 3478)
  hi := (22 / 47)
  vmin := (3008245 / 12096484)
  damping := (3008245 / 12096484)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell030
