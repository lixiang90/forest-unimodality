import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell318
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (33)
  A := (10688599588524338450667983 / 500000000000000000000000000)
  B := (17748319916855492817120421 / 1000000000000000000000000000)
  C := (35182615627373667321897699 / 1000000000000000000000000000)
  dδ := (14016839100891952465954837 / 1000000000000000000000000000)
  dM := (5558790638700501670873069 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(479210959912722174180999 / 40000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236 / 371)
  hi := (9 / 14)
  vmin := (45 / 196)
  damping := (45 / 196)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell318
