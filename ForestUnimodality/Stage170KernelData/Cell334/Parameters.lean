import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell334
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (55685908840752261781403831 / 1000000000000000000000000000)
  B := (1790741562422778262314571 / 125000000000000000000000000)
  C := (11456886936170317808914021 / 500000000000000000000000000)
  dδ := (2918060732814720895783589 / 250000000000000000000000000)
  dM := (8318233921314428574653177 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(9021109892037150856936023 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 3)
  hi := (35 / 52)
  vmin := (595 / 2704)
  damping := (1487500000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell334
