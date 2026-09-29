import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell532
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (78)
  A := (-365149705066752143856057 / 312500000000000000000000)
  B := (78891333453623438409785251 / 1000000000000000000000000000)
  C := (19671119158338154497833727 / 100000000000000000000000000)
  dδ := (10360247280685512538678239 / 250000000000000000000000000)
  dM := (37254025631886769544948157 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(44839568444378512523940117 / 10000000000000000000000000), (13779449120853601851166559 / 5000000000000000000000000), (13106933645001209498559547 / 500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99 / 179)
  hi := (5 / 9)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell532
