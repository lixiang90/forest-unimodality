import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell450
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (-23385674863086996055017153 / 100000000000000000000000000)
  B := (37356366733854833028782849 / 1000000000000000000000000000)
  C := (-11862440402959131824367489 / 100000000000000000000000000)
  dδ := (238529144751250504752349 / 8000000000000000000000000)
  dM := (15723934790103582343975819 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7826487172463897579177683 / 2000000000000000000000000), (3984031078504696665731899 / 200000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64 / 153)
  hi := (65 / 153)
  vmin := (5696 / 23409)
  damping := (5696 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell450
