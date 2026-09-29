import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (258)
  A := (-17670447216706565607324819 / 10000000000000000000000000)
  B := (498013958330105546701283 / 10000000000000000000000000)
  C := (3325142356228193325773379 / 2000000000000000000000000000)
  dδ := (29576335633784790746236837 / 1000000000000000000000000000)
  dM := (12620881254211843659415737 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(46114935264692377359097009 / 1000000000000000000000000), (21009011624918133520623087 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109 / 209)
  hi := (11 / 21)
  vmin := (110 / 441)
  damping := (110 / 441)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell186
