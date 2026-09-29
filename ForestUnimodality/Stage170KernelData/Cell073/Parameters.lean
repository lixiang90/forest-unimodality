import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (54)
  A := (15605142855215610065755527 / 100000000000000000000000000)
  B := (5199202831661193027756873 / 500000000000000000000000000)
  C := (-36932300612261138861303067 / 1000000000000000000000000000)
  dδ := (10705113358900257211625551 / 1000000000000000000000000000)
  dM := (22127487495287844203491201 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10065321968147509235080861 / 2500000000000000000000000), (17470530521439631144176019 / 1000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell073
