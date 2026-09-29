import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell267
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (78)
  A := (-20379829426759303977689797 / 100000000000000000000000000)
  B := (97047879297673736442853 / 5000000000000000000000000)
  C := (326407546644105830968563 / 5000000000000000000000000)
  dδ := (2776643001190497173080729 / 200000000000000000000000000)
  dM := (91430981528509196404677639 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(17033414562336623987448547 / 1000000000000000000000000), (16052616376280262500131357 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 187)
  hi := (27 / 47)
  vmin := (540 / 2209)
  damping := (540 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell267
