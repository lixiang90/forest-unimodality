import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell414
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (41)
  A := (13958573349963970855469597 / 5000000000000000000000000000)
  B := (28262664504178781899046413 / 1000000000000000000000000000)
  C := (16617984459929588392235189 / 200000000000000000000000000)
  dδ := (6482708634047613244222319 / 250000000000000000000000000)
  dM := (24018886404062755077042091 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(16293780957834023581654037 / 1000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell414
