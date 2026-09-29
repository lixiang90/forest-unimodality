import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell050
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 21
  density := (16980753671294274694327282849 / 62500000000000000000000000000)
  probabilityCap := (8999 / 18624)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (62, 17), (62, 18), (62, 19), (62, 20), (62, 21), (63, 18), (63, 19), (63, 20), (63, 21), (64, 18), (64, 19), (64, 20), (64, 21), (65, 18), (65, 19), (65, 20), (65, 21), (66, 18), (66, 19), (66, 20), (66, 21), (67, 19), (67, 20), (67, 21), (68, 19), (68, 20), (68, 21), (69, 19), (69, 20), (69, 21), (70, 20), (70, 21), (71, 20), (71, 21), (72, 20), (72, 21), (73, 20), (73, 21), (74, 21), (75, 21), (76, 21), (77, 21)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (4487 / 4825)
def activityUpper : ℚ := (8999 / 9625)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (644646871911563251944699 / 200000000000000000000000)
  B := (-7694643918226405643334687 / 100000000000000000000000000)
  C := (-9291088796351087975011751 / 100000000000000000000000000)
  dδ := (328816960021233450905953 / 2500000000000000000000000)
  dM := (827271378168870927867929 / 12500000000000000000000000000)
  wL := (2769336041289 / 1250000000000)
  wR := (4461327917421 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(1403586851850691097354229 / 200000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (1102847579894224949725867 / 50000000000000000000000) else if j = 0 then (623481212250429628340953 / 50000000000000000000000) else if j = 1 then (2595488151234366469566339 / 100000000000000000000000) else if j = 2 then (524680151421847273951471 / 25000000000000000000000) else if j = 3 then (67665860850698740236453 / 5000000000000000000000) else if j = 4 then (495391563022458569776063 / 25000000000000000000000) else if j = 5 then (297964401380409027453311 / 12500000000000000000000) else if j = 6 then (407659003743114993767449 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (25417236200476995723598929 / 1000000000000000000000000000000) else if j = 0 then (24603729818852130299093283 / 500000000000000000000000000000) else if j = 1 then (18347483321726784099330389 / 200000000000000000000000000000) else if j = 2 then (75965290190209450417312741 / 500000000000000000000000000000) else if j = 3 then (209434313642377292116473497 / 1000000000000000000000000000000) else if j = 4 then (232618762160807605925310291 / 1000000000000000000000000000000) else if j = 5 then (232618762160807605925310291 / 1000000000000000000000000000000) else if j = 6 then (232618762160807605925310291 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (4487 / 9312)
  hi := (8999 / 18624)
  vmin := (21649775 / 86713344)
  damping := (21649775 / 86713344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell050
