import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (246)
  A := (-2036294236539735931490469 / 1250000000000000000000000)
  B := (24283990659727239941334531 / 500000000000000000000000000)
  C := (-18238090879534078151552601 / 10000000000000000000000000000)
  dδ := (30922100809656526826385559 / 1000000000000000000000000000)
  dM := (25415357923667627375666211 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(25873522283915143304966477 / 1000000000000000000000000), (873873416140525478112977 / 4000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (23 / 48)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell131
