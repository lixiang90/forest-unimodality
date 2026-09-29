import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell419
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (31)
  A := (5059528246350312119972159 / 50000000000000000000000000)
  B := (22898920102380315722001569 / 1000000000000000000000000000)
  C := (56634116347653799816708187 / 1000000000000000000000000000)
  dδ := (22205589755003987684212063 / 1000000000000000000000000000)
  dM := (18947929281627027436364641 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2302315837533063458408833 / 200000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467 / 742)
  hi := (236 / 371)
  vmin := (31860 / 137641)
  damping := (31860 / 137641)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell419
