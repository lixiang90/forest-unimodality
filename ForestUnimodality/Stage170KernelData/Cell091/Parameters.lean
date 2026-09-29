import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (76)
  A := (7656969440214910775921453 / 500000000000000000000000000)
  B := (15011388292526408119731407 / 1000000000000000000000000000)
  C := (-12712069743651072117884837 / 200000000000000000000000000)
  dδ := (438491127482140891948037 / 31250000000000000000000000)
  dM := (6902071467555503665302491 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(19450420375214694246324143 / 2500000000000000000000000), (1222257271167163494851593 / 50000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64 / 153)
  hi := (65 / 153)
  vmin := (5696 / 23409)
  damping := (5696 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell091
