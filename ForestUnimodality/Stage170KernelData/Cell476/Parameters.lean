import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell476
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-10152107743085154406514903 / 5000000000000000000000000)
  B := (10745589064135376011765999 / 100000000000000000000000000)
  C := (-12944858459372442487794741 / 10000000000000000000000000000)
  dδ := (2850266970310225828066919 / 50000000000000000000000000)
  dM := (5290118211342380999395729 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(47452821597892649307937063 / 10000000000000000000000000), (91168595438033449340764491 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4777 / 9702)
  hi := (3193 / 6468)
  vmin := (23526725 / 94128804)
  damping := (23526725 / 94128804)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell476
