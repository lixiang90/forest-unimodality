import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (294)
  A := (-8901493457208462195495713 / 5000000000000000000000000)
  B := (46718574389025144255604971 / 1000000000000000000000000000)
  C := (10129197986590620446552269 / 50000000000000000000000000000)
  dδ := (28096064135691406482564503 / 1000000000000000000000000000)
  dM := (22003775761586530108210313 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1365649701135662397177839 / 25000000000000000000000), (23756582978295580232952489 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell157
