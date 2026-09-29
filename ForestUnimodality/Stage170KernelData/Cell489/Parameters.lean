import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell489
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-4480791635389484275897587 / 2500000000000000000000000)
  B := (19233581654989354015050651 / 200000000000000000000000000)
  C := (2303236801784504846762891 / 2000000000000000000000000000)
  dδ := (55937872014290491995414101 / 1000000000000000000000000000)
  dM := (92606668432828286290775521 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(11057994480721742291962073 / 1000000000000000000000000), (22523728152877264818698677 / 250000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3493 / 6868)
  hi := (26 / 51)
  vmin := (650 / 2601)
  damping := (650 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell489
