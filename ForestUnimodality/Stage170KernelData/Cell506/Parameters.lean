import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell506
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-9713594216561186273040107 / 5000000000000000000000000)
  B := (415583197388817271455963 / 4000000000000000000000000)
  C := (29786823056187285325979719 / 10000000000000000000000000000)
  dδ := (57610421721836460595689289 / 1000000000000000000000000000)
  dM := (508298529835042611248197 / 500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(91359247297163825862753583 / 10000000000000000000000000), (89866734687555165805861179 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109 / 209)
  hi := (4583 / 8778)
  vmin := (19225685 / 77053284)
  damping := (19225685 / 77053284)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell506
