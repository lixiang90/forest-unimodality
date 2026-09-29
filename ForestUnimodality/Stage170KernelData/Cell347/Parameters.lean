import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell347
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (25)
  A := (12453317575817679232486057 / 250000000000000000000000000)
  B := (12073696509000111237730479 / 1000000000000000000000000000)
  C := (8147684426519674269484561 / 500000000000000000000000000)
  dδ := (19202687863256219513719003 / 2000000000000000000000000000)
  dM := (30899600052895267586917233 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(3957268315947504166985027 / 12500000000000000000000000), (75599091948071794888619479 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell347
