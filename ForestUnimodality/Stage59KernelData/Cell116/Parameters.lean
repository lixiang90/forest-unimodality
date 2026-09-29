import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell116
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (17616631309669530073104738771 / 62500000000000000000000000000)
  probabilityCap := (3579 / 7004)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (26 / 25)
def activityUpper : ℚ := (3579 / 3425)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (252352786007874725250133 / 1000000000000000000000000)
  B := (4003847179512780296573027 / 50000000000000000000000000)
  C := (4429434168448707215270943 / 50000000000000000000000000)
  dδ := (1358235055483884567983921 / 10000000000000000000000000)
  dM := (1220078865040681538253753 / 500000000000000000000000000)
  wL := (4544012688657 / 2500000000000)
  wR := (2727993655671 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(2167614194911802183440841 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (7680422473241435010749 / 312500000000000000000) else if j = 0 then (296820762389484382737237 / 12500000000000000000000) else if j = 1 then (1626265458618984283134523 / 50000000000000000000000) else if j = 2 then (3908857851186316167968471 / 100000000000000000000000) else if j = 3 then (22783865698541491684459 / 1562500000000000000000) else if j = 4 then (1425435299687477375130129 / 100000000000000000000000) else if j = 5 then (181229247206032595407521 / 12500000000000000000000) else if j = 6 then (1651675591936224662958921 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (27067119541089889200814339 / 1000000000000000000000000000000) else if j = 0 then (181189869699776257985919 / 3906250000000000000000000000) else if j = 1 then (81798553388120949437828743 / 1000000000000000000000000000000) else if j = 2 then (16005890843169768141406897 / 125000000000000000000000000000) else if j = 3 then (79649319898534107459753237 / 500000000000000000000000000000) else if j = 4 then (79649319898534107459753237 / 500000000000000000000000000000) else if j = 5 then (79649319898534107459753237 / 500000000000000000000000000000) else if j = 6 then (79649319898534107459753237 / 500000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (26 / 51)
  hi := (3579 / 7004)
  vmin := (12258075 / 49056016)
  damping := (12258075 / 49056016)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell116
