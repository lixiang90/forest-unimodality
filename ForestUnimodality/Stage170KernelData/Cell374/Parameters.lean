import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell374
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (77)
  A := (-15284241854027506596125363 / 25000000000000000000000000)
  B := (23476305885817162072415343 / 500000000000000000000000000)
  C := (-3885498062545227060393671 / 25000000000000000000000000)
  dδ := (16107951576236522600593659 / 500000000000000000000000000)
  dM := (1863250978923583522136459 / 5000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6963546702395389864648223 / 1000000000000000000000000), (26459680020011447254546511 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67 / 153)
  hi := (4 / 9)
  vmin := (5762 / 23409)
  damping := (5762 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell374
