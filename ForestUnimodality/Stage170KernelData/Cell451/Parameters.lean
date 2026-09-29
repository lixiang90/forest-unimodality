import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell451
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (61)
  A := (-7230270559982233469042967 / 20000000000000000000000000)
  B := (8312063738461841766458349 / 200000000000000000000000000)
  C := (-13102178848605686156680861 / 100000000000000000000000000)
  dδ := (7818576290482553634020313 / 250000000000000000000000000)
  dM := (35122916179901233352245171 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1599784692665834062719199 / 625000000000000000000000), (27818385438943238341380493 / 5000000000000000000000000), (8833296636247499833416441 / 500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65 / 153)
  hi := (22 / 51)
  vmin := (5720 / 23409)
  damping := (5720 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell451
