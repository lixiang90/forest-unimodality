import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell271
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (69)
  A := (-12404940307992473102594033 / 50000000000000000000000000)
  B := (23125097173680206341650489 / 1000000000000000000000000000)
  C := (17818459303657628589601103 / 250000000000000000000000000)
  dδ := (7967012797082503178236479 / 500000000000000000000000000)
  dM := (12673554338604346236954457 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(71403066535852106611059753 / 10000000000000000000000000), (21886098805105710596308199 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 47)
  hi := (653 / 1128)
  vmin := (310175 / 1272384)
  damping := (310175 / 1272384)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell271
