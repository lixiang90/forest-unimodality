import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-3409075181498435697058369/5000000000000000000000000)
  B := (2972755615960000555308973/31250000000000000000000000)
  C := (49550206728722163626588149/10000000000000000000000000000)
  dδ := (91758696998041178183314059/1000000000000000000000000000)
  dM := (7918675437582411514095271/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(73303888328286115338983109/10000000000000000000000000), (8380200490877356855889957/200000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell120
