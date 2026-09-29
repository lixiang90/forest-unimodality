import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell544
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (39)
  A := (1210544536166003771526789 / 100000000000000000000000000)
  B := (27419966350302353574885927 / 1000000000000000000000000000)
  C := (4074462676301940367018517 / 50000000000000000000000000)
  dδ := (25557638690796542074723519 / 1000000000000000000000000000)
  dM := (23786635147521702953257727 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15505068553144651488651107 / 1000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell544
