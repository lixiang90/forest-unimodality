import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell346
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (23)
  A := (34721400748056473481994999 / 1000000000000000000000000000)
  B := (6695086815112452627296591 / 500000000000000000000000000)
  C := (4411980715915091340317833 / 250000000000000000000000000)
  dδ := (1300809351366736263747037 / 125000000000000000000000000)
  dM := (7626315307845713486155359 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5826675894187370197130349 / 2000000000000000000000000), (43176980303387502146961197 / 10000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell346
