import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell156
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (143441362524892641522403116519 / 500000000000000000000000000000)
  probabilityCap := (1549 / 2954)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (11 / 10)
def activityUpper : ℚ := (1549 / 1405)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (226586019244596018472393 / 62500000000000000000000)
  B := (-135500889231303899007397 / 1562500000000000000000000)
  C := (2823352599091105141759783 / 10000000000000000000000000)
  dδ := (1628745688739909602826827 / 10000000000000000000000000)
  dM := (212052739800170215967931 / 1000000000000000000000000000)
  wL := (905405743231 / 625000000000)
  wR := (255135081083 / 100000000000)
  wC := (1 / 10000000000000)
  price := ![(8147673576371246895178047 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4}
  fixedPrice := fun j => if j = -1 then (2662064679875249240126323 / 100000000000000000000000) else if j = 0 then (2280965946086449847030053 / 100000000000000000000000) else if j = 1 then (3524096255646447417575473 / 100000000000000000000000) else if j = 2 then (918967678476020495281773 / 20000000000000000000000) else if j = 3 then (2863153026501715814333693 / 100000000000000000000000) else if j = 4 then (2168903275867611057936557 / 2500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (27448969915205533480359767 / 1000000000000000000000000000000) else if j = 0 then (22142193572459911125688369 / 500000000000000000000000000000) else if j = 1 then (18418100238300991999506783 / 250000000000000000000000000000) else if j = 2 then (22274526218905008615715111 / 200000000000000000000000000000) else if j = 3 then (1025974977274400778642563 / 7812500000000000000000000000) else if j = 4 then (1025974977274400778642563 / 7812500000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (1549 / 2954)
  vmin := (2176345 / 8726116)
  damping := (2176345 / 8726116)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell156
