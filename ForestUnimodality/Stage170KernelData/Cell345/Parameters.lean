import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell345
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (22)
  A := (8164455846736145554487507 / 500000000000000000000000000)
  B := (2226898891613247801618547 / 125000000000000000000000000)
  C := (2786384905844838631716609 / 125000000000000000000000000)
  dδ := (6690889948884589169542103 / 500000000000000000000000000)
  dM := (3103545331232339848969229 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(41438708949293096006627479 / 100000000000000000000000000), (64765353733124220170225271 / 10000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 156)
  hi := (9 / 13)
  vmin := (36 / 169)
  damping := (1440000000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell345
