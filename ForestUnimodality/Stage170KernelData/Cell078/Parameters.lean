import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (999953996558141755635063 / 10000000000000000000000000)
  B := (98963735586861199117203469 / 10000000000000000000000000000)
  C := (-35212988268664452418121869 / 1000000000000000000000000000)
  dδ := (93231090953163082285515273 / 10000000000000000000000000000)
  dM := (147668536940619772643071 / 3906250000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(64399210348407152082472749 / 10000000000000000000000000), (912738197686373275985261 / 50000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101 / 255)
  hi := (103 / 255)
  vmin := (15554 / 65025)
  damping := (15554 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell078
