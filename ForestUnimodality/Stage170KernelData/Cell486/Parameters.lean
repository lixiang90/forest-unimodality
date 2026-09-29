import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell486
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (104)
  A := (-9394814293553611311793361 / 5000000000000000000000000)
  B := (98473048382711522719112907 / 1000000000000000000000000000)
  C := (76351326197107954700527 / 125000000000000000000000000)
  dδ := (6884129656596757983189061 / 125000000000000000000000000)
  dM := (93975903554873797037666483 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(94039476198437039755617661 / 10000000000000000000000000), (9266263729480237998359371 / 100000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51 / 101)
  hi := (10429 / 20604)
  vmin := (106115075 / 424524816)
  damping := (106115075 / 424524816)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell486
