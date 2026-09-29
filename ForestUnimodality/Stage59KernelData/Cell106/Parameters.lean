import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell106
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (139834119030299925755241366451 / 500000000000000000000000000000)
  probabilityCap := (51 / 101)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (407 / 401)
def activityUpper : ℚ := (51 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (30)
  A := (525595428959939223041431 / 1250000000000000000000000)
  B := (3078377583015294571833209 / 50000000000000000000000000)
  C := (9510296932349959070363 / 250000000000000000000000)
  dδ := (628386134954386221806999 / 5000000000000000000000000)
  dM := (1898827541572370783407031 / 1000000000000000000000000000)
  wL := (512174547529 / 1250000000000)
  wR := (1344876474597 / 2500000000000)
  wC := (1526154886069 / 2000000000000)
  price := ![(5492184457638575878490883 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (256662363704581899526147 / 10000000000000000000000) else if j = 0 then (96816161415983987836853 / 5000000000000000000000) else if j = 1 then (2393992712914022646941703 / 100000000000000000000000) else if j = 2 then (64953237968286203773971 / 3125000000000000000000) else if j = 3 then (1460554852860957097959727 / 100000000000000000000000) else if j = 4 then (370122233164748415390477 / 25000000000000000000000) else if j = 5 then (1015644946521340763467833 / 100000000000000000000000) else if j = 6 then (524453564398937910340237 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13215405883269206343341959 / 500000000000000000000000000000) else if j = 0 then (5800338011532882890392131 / 125000000000000000000000000000) else if j = 1 then (3353327549467553037212101 / 40000000000000000000000000000) else if j = 2 then (16691697026294209427865171 / 125000000000000000000000000000) else if j = 3 then (170189852032803703970389979 / 1000000000000000000000000000000) else if j = 4 then (8663510567280731536954241 / 50000000000000000000000000000) else if j = 5 then (8663510567280731536954241 / 50000000000000000000000000000) else if j = 6 then (8663510567280731536954241 / 50000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (407 / 808)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell106
