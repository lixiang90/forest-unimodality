import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell416
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (37)
  A := (51370776691248297716185789 / 1000000000000000000000000000)
  B := (5215294868761328334061389 / 200000000000000000000000000)
  C := (714107237915312248466293 / 10000000000000000000000000)
  dδ := (24404674596095334015988243 / 1000000000000000000000000000)
  dM := (21873204161456478653025037 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(14324497417138575272588241 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63 / 103)
  hi := (129 / 209)
  vmin := (10320 / 43681)
  damping := (10320 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell416
