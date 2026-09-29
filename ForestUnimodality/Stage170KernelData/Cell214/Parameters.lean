import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (129)
  A := (-11596689352922896942743591 / 10000000000000000000000000)
  B := (56005638254729296632294933 / 1000000000000000000000000000)
  C := (21696071468943525784034421 / 100000000000000000000000000)
  dδ := (3536737570957865922638419 / 100000000000000000000000000)
  dM := (37568153280496686388309491 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(91417702822587472155646537 / 10000000000000000000000000), (24584232457136089067262219 / 500000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 54)
  hi := (643 / 1188)
  vmin := (350435 / 1411344)
  damping := (350435 / 1411344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell214
