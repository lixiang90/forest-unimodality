import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell546
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (35)
  A := (51182424786870693864671011 / 1000000000000000000000000000)
  B := (26938326735427495228769601 / 1000000000000000000000000000)
  C := (3671037875732031940945177 / 50000000000000000000000000)
  dδ := (25340614312507499933380117 / 1000000000000000000000000000)
  dM := (11998746272591403788827791 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6772332031334229895946919 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63 / 103)
  hi := (129 / 209)
  vmin := (10320 / 43681)
  damping := (10320 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell546
