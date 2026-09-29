import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell264
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (63)
  A := (-31991035968428043311462261 / 100000000000000000000000000)
  B := (35222676984817305467778681 / 1000000000000000000000000000)
  C := (266512033525207261974721 / 2500000000000000000000000)
  dδ := (25149253318917260541232039 / 1000000000000000000000000000)
  dM := (26196553740797463762784991 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(34023616090129418232379521 / 10000000000000000000000000), (360903994098871749862667 / 15625000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell264
