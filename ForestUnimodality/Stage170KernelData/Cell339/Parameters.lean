import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell339
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (237781539829225779847377 / 5000000000000000000000000)
  B := (6125093673522743510651001 / 500000000000000000000000000)
  C := (9106275072490670197122853 / 500000000000000000000000000)
  dδ := (24182954930263601822648667 / 2500000000000000000000000000)
  dM := (62944874845329424999096357 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(4423301826385915624939571 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35 / 52)
  hi := (53 / 78)
  vmin := (1325 / 6084)
  damping := (13250000000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell339
