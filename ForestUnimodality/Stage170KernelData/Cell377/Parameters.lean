import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell377
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (116)
  A := (-15348412894858036070644403 / 10000000000000000000000000)
  B := (87950244556152995523135019 / 1000000000000000000000000000)
  C := (-29370443710922822244668851 / 100000000000000000000000000)
  dδ := (3306784932084453135225921 / 62500000000000000000000000)
  dM := (76950369993400045617870653 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(11011368089371209588733791 / 1250000000000000000000000), (43107046061856053142946621 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17 / 37)
  hi := (1613 / 3478)
  vmin := (340 / 1369)
  damping := (340 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell377
