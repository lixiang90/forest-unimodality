import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell192
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (285)
  A := (-4839582332915847553955757 / 2500000000000000000000000)
  B := (5112607817745977445422767 / 100000000000000000000000000)
  C := (8794926302824028225418873 / 5000000000000000000000000000)
  dδ := (14454934174255942153086707 / 500000000000000000000000000)
  dM := (49465243111787668851137 / 200000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(6848958312412080751130361 / 125000000000000000000000), (11412267984222452810172399 / 50000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (111 / 211)
  vmin := (11100 / 44521)
  damping := (11100 / 44521)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell192
