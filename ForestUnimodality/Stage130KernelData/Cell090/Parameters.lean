import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 90
  A := (-7977905154369140056047627/5000000000000000000000000)
  B := (97234580575487603026907379/1000000000000000000000000000)
  C := (21647561985867051249921023/10000000000000000000000000000)
  dδ := (60618613046867136917583707/1000000000000000000000000000)
  dM := (1285078607693468399388037/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12004892709901218594836791/1000000000000000000000000), (23945081710796031870813749/1000000000000000000000000), (818687510805947260550397/15625000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/103)
  hi := (21967/42642)
  vmin := (454167725/1818340164)
  damping := (454167725/1818340164)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell090
