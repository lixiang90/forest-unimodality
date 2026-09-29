import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 86
  A := (-26424177239772610569445987/100000000000000000000000000)
  B := (6960235728070340854856113/50000000000000000000000000)
  C := (36006274745450117524825373/50000000000000000000000000)
  dδ := (9135668994162771117117927/50000000000000000000000000)
  dM := (30194934478259337178041033/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(17375929445478682566772477/2000000000000000000000000), (15165940258960572961655089/500000000000000000000000)]
  retention := ![(7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell174
