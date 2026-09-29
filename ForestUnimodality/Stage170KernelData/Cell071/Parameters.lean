import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (15578432332731008026271979 / 100000000000000000000000000)
  B := (6968944673578204851427387 / 500000000000000000000000000)
  C := (-48939291569930404302013471 / 1000000000000000000000000000)
  dδ := (14701912324609751545057001 / 1000000000000000000000000000)
  dM := (624810288872086790068483 / 8000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(479874548431616254617893 / 250000000000000000000000), (3357668240043219753943049 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 85)
  hi := (101 / 255)
  vmin := (1716 / 7225)
  damping := (1716 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell071
