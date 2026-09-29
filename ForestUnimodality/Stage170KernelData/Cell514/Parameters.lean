import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell514
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-4351101331311756450475059 / 2000000000000000000000000)
  B := (227307515929850850744387 / 2000000000000000000000000)
  C := (41226077096275697345117983 / 10000000000000000000000000000)
  dδ := (7324695355080159710203791 / 125000000000000000000000000)
  dM := (5577083717138035844421151 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(39556149665705060414211403 / 10000000000000000000000000), (23703592353160811256884699 / 250000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111 / 211)
  hi := (23557 / 44732)
  vmin := (498819475 / 2000951824)
  damping := (498819475 / 2000951824)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell514
