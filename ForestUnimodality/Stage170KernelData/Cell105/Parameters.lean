import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (93)
  A := (-75542069787456016637605671 / 100000000000000000000000000)
  B := (47933184970443992733990513 / 1000000000000000000000000000)
  C := (-17307401979206030184776921 / 100000000000000000000000000)
  dδ := (2041608678904062185860413 / 62500000000000000000000000)
  dM := (35171010954684769986983151 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(12945080564263403033464783 / 1000000000000000000000000), (562506010214780829414849 / 20000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4 / 9)
  hi := (301 / 666)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell105
