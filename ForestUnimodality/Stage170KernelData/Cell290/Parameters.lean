import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell290
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (47)
  A := (-771310000036300465131589 / 6250000000000000000000000)
  B := (6319181109452566905138049 / 250000000000000000000000000)
  C := (6222628935154900231552233 / 100000000000000000000000000)
  dδ := (2306821870842295108677833 / 125000000000000000000000000)
  dM := (17054032888566536866302437 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(9297959767837951972069277 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3 / 5)
  hi := (123 / 203)
  vmin := (9840 / 41209)
  damping := (9840 / 41209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell290
