import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (91)
  A := (-20106780201314221722341813 / 100000000000000000000000000)
  B := (18078265425277465633380203 / 1000000000000000000000000000)
  C := (-37411018921300893957937461 / 500000000000000000000000000)
  dδ := (7099541256121442642235131 / 500000000000000000000000000)
  dM := (80811878603192190064115341 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(89257385417541765804116949 / 10000000000000000000000000), (3829231967311184092750409 / 125000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell099
