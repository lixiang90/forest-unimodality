import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell440
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (30)
  A := (188729018282168410647337 / 1250000000000000000000000)
  B := (17006942902107066717398709 / 1000000000000000000000000000)
  C := (-39501278067651926506620441 / 1000000000000000000000000000)
  dδ := (2209883652918568329448501 / 125000000000000000000000000)
  dM := (5738210535542816490917409 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(27258627567804083469127363 / 50000000000000000000000000), (16706861592061179599966181 / 10000000000000000000000000), (41742711960269618387542323 / 5000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 85)
  hi := (89 / 255)
  vmin := (1624 / 7225)
  damping := (2598400000000000000000000000000000000000000 / 28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell440
