import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell223
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 53
  A := (-12350594122132222990373407/25000000000000000000000000)
  B := (31631248847586564132416953/500000000000000000000000000)
  C := (8350584424904565483682717/50000000000000000000000000)
  dδ := (22088866267277396798762723/500000000000000000000000000)
  dM := (17649321537485180210955149/25000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(50746415276804830440937621/10000000000000000000000000), (4332605350193427184990469/2000000000000000000000000), (14727649402748561158205121/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/187)
  hi := (27/47)
  vmin := (540/2209)
  damping := (540/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell223
