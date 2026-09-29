import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell120
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (141361009715896245121689758251 / 500000000000000000000000000000)
  probabilityCap := (10787 / 21012)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (5381 / 5125)
def activityUpper : ℚ := (10787 / 10225)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (407282157258272931233023 / 200000000000000000000000)
  B := (-216451440753473358519221 / 12500000000000000000000000)
  C := (1468312708017245060698741 / 20000000000000000000000000)
  dδ := (1291109720333039889705873 / 10000000000000000000000000)
  dM := (9794608713346417312728409 / 10000000000000000000000000000)
  wL := (4569450953043 / 2500000000000)
  wR := (1357637261739 / 625000000000)
  wC := (1 / 10000000000000)
  price := ![(5244934506623327941099433 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2413970873456049659466771 / 100000000000000000000000) else if j = 0 then (1286240576149897307800529 / 50000000000000000000000) else if j = 1 then (729464156764457527515333 / 20000000000000000000000) else if j = 2 then (2000901009982849743096267 / 50000000000000000000000) else if j = 3 then (162447476239264751995961 / 10000000000000000000000) else if j = 4 then (1800965290820555253503699 / 100000000000000000000000) else if j = 5 then (2027028923341586974515849 / 100000000000000000000000) else if j = 6 then (2692024099085389465813023 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (6833237044333772871012697 / 250000000000000000000000000000) else if j = 0 then (11599041014664565815249907 / 250000000000000000000000000000) else if j = 1 then (20260846667514572859271517 / 250000000000000000000000000000) else if j = 2 then (125998349270744477384597649 / 1000000000000000000000000000000) else if j = 3 then (77632013427337117161155291 / 500000000000000000000000000000) else if j = 4 then (77632013427337117161155291 / 500000000000000000000000000000) else if j = 5 then (77632013427337117161155291 / 500000000000000000000000000000) else if j = 6 then (77632013427337117161155291 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (5381 / 10506)
  hi := (10787 / 21012)
  vmin := (110297075 / 441504144)
  damping := (110297075 / 441504144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell120
