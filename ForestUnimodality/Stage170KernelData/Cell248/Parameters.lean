import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell248
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (91)
  A := (-35625998352174885862808651 / 100000000000000000000000000)
  B := (22977449013494809920699069 / 1000000000000000000000000000)
  C := (42100861414228481216515121 / 500000000000000000000000000)
  dδ := (15904386230007724195578689 / 1000000000000000000000000000)
  dM := (5570091446319434856995767 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(344074062185086830822911 / 20000000000000000000000), (11172385858019920235051359 / 500000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116 / 207)
  hi := (13 / 23)
  vmin := (130 / 529)
  damping := (130 / 529)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell248
