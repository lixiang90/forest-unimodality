import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell403
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (75)
  A := (-48091739887755432569349523 / 50000000000000000000000000)
  B := (64746417109029230640970809 / 1000000000000000000000000000)
  C := (16849435311067317844191393 / 100000000000000000000000000)
  dδ := (17703060253634952947443537 / 500000000000000000000000000)
  dM := (28518756816403822941172197 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(38245674179144746318570469 / 5000000000000000000000000), (24518473226131330733323921 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5 / 9)
  hi := (116 / 207)
  vmin := (10556 / 42849)
  damping := (10556 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell403
