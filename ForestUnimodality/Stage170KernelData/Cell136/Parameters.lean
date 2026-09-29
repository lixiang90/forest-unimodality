import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (242)
  A := (-8171186706737140986689383 / 5000000000000000000000000)
  B := (9843668239212971515783579 / 200000000000000000000000000)
  C := (-720857028253744274229331 / 500000000000000000000000000)
  dδ := (31215236707615594963227679 / 1000000000000000000000000000)
  dM := (6511002227918714013125273 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(26234053706447934217749207 / 1000000000000000000000000), (5352548635738838100905923 / 25000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23 / 48)
  hi := (47 / 97)
  vmin := (575 / 2304)
  damping := (575 / 2304)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell136
