import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell453
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (74)
  A := (-9952628357905438663433273 / 12500000000000000000000000)
  B := (29137548167128917570023461 / 500000000000000000000000000)
  C := (-4243582986022385872271201 / 25000000000000000000000000)
  dδ := (3604453776142943488558501 / 100000000000000000000000000)
  dM := (25421328098477140701796917 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7300845852116687240140891 / 500000000000000000000000), (17285209058819841487775193 / 1000000000000000000000000)]
  retention := ![(3 / 5), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell453
