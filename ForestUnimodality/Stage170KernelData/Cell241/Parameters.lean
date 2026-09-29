import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell241
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (80)
  A := (-36456673630647104033641881 / 50000000000000000000000000)
  B := (24497617167805015719883599 / 500000000000000000000000000)
  C := (14990781176250422834783649 / 100000000000000000000000000)
  dδ := (15275230777343115975974719 / 500000000000000000000000000)
  dM := (18675101928572473844805679 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(21148015005817868972037843 / 100000000000000000000000000), (724613680226686511787193 / 40000000000000000000000), (3263830330780017163760931 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5 / 9)
  hi := (116 / 207)
  vmin := (10556 / 42849)
  damping := (10556 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell241
