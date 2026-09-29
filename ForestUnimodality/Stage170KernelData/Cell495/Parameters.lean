import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell495
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-17397794192447534788925623 / 10000000000000000000000000)
  B := (4774357693891729398361079 / 50000000000000000000000000)
  C := (23643684624774928722257261 / 10000000000000000000000000000)
  dδ := (11580318831257528644496091 / 200000000000000000000000000)
  dM := (4632223329611566972965897 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(98535718687768980572627697 / 10000000000000000000000000), (91351121486284526440613263 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21967 / 42642)
  hi := (10996 / 21321)
  vmin := (113533700 / 454585041)
  damping := (113533700 / 454585041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell495
