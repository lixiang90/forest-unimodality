import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (90)
  A := (-82785906105508770934875429 / 100000000000000000000000000)
  B := (26644430081621248151968473 / 500000000000000000000000000)
  C := (1065641536590730513445191 / 6250000000000000000000000)
  dδ := (4107206342768642860774353 / 125000000000000000000000000)
  dM := (20470374597480274405508771 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1570195969084378528890511 / 500000000000000000000000), (7359301696774038781256877 / 1000000000000000000000000), (28918535209652642237188047 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 89)
  hi := (99 / 179)
  vmin := (7920 / 32041)
  damping := (7920 / 32041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell231
