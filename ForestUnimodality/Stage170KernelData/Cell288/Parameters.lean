import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell288
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (-23306580058918906459553 / 4000000000000000000000000)
  B := (7364049554463917603153167 / 500000000000000000000000000)
  C := (703047844524259707595093 / 15625000000000000000000000)
  dδ := (601017631272934491071247 / 50000000000000000000000000)
  dM := (34726053414852692887045127 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5898666510218877334637 / 400000000000000000000), (8307168331429734209336857 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 180)
  hi := (3 / 5)
  vmin := (6 / 25)
  damping := (6 / 25)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell288
