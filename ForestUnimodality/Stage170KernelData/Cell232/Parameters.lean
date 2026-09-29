import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (97)
  A := (-65559631120719212947989263 / 100000000000000000000000000)
  B := (40825867525393605417249887 / 1000000000000000000000000000)
  C := (14801225317015753724092519 / 100000000000000000000000000)
  dδ := (2738886001623884111633167 / 100000000000000000000000000)
  dM := (13370561519824447366949771 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15178453267593354780728987 / 2000000000000000000000000), (35175291559787247308577207 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell232
