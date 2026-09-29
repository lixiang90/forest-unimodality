import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell052
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (136092992956619134621855462741 / 500000000000000000000000000000)
  probabilityCap := (47 / 97)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 18), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21), (77, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (8999 / 9625)
def activityUpper : ℚ := (47 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (206953757679043734839297 / 62500000000000000000000)
  B := (-818532496301288547968511 / 10000000000000000000000000)
  C := (-255655620056995346034423 / 2500000000000000000000000)
  dδ := (1327184503523237968369841 / 10000000000000000000000000)
  dM := (0)
  wL := (5563594926697 / 2500000000000)
  wR := (2218202536651 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(7173253656007856804421863 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1089324263457177011105159 / 50000000000000000000000) else if j = 0 then (279772029310966852122533 / 25000000000000000000000) else if j = 1 then (26095566659345067250797 / 1000000000000000000000) else if j = 2 then (1059336048308842670451213 / 50000000000000000000000) else if j = 3 then (136979722050652146236871 / 10000000000000000000000) else if j = 4 then (402826800299996605758679 / 20000000000000000000000) else if j = 5 then (1215930164913531008608061 / 50000000000000000000000) else if j = 6 then (2085338119065229633974923 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25568669700072263130279299 / 1000000000000000000000000000000) else if j = 0 then (4923528011048802081415191 / 100000000000000000000000000000) else if j = 1 then (45648618475031398081357999 / 500000000000000000000000000000) else if j = 2 then (150828426387642948559406509 / 1000000000000000000000000000000) else if j = 3 then (207100958309011888559220633 / 1000000000000000000000000000000) else if j = 4 then (28599252630643008342363733 / 125000000000000000000000000000) else if j = 5 then (28599252630643008342363733 / 125000000000000000000000000000) else if j = 6 then (28599252630643008342363733 / 125000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (8999 / 18624)
  hi := (47 / 97)
  vmin := (86615375 / 346853376)
  damping := (86615375 / 346853376)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell052
