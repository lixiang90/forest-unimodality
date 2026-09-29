import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell417
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (35)
  A := (53391832605068477732856991 / 1000000000000000000000000000)
  B := (25535776404615236762074559 / 1000000000000000000000000000)
  C := (65785366197109035324430693 / 1000000000000000000000000000)
  dδ := (23486095869194943686064647 / 1000000000000000000000000000)
  dM := (21357136022586735630592047 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6680629778570818189109559 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129 / 209)
  hi := (33 / 53)
  vmin := (660 / 2809)
  damping := (660 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell417
