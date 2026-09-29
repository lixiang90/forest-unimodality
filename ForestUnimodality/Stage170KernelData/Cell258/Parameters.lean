import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell258
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (86)
  A := (-28486047883177949668009887 / 100000000000000000000000000)
  B := (2669485922467167409583011 / 125000000000000000000000000)
  C := (72838096953207712158651077 / 1000000000000000000000000000)
  dδ := (7368597553201954031276699 / 500000000000000000000000000)
  dM := (99875303686651023494721957 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(3031558943495921454314157 / 200000000000000000000000), (433179374016363851751521 / 20000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21 / 37)
  hi := (53 / 93)
  vmin := (2120 / 8649)
  damping := (2120 / 8649)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell258
