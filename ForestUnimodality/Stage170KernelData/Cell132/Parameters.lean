import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (272)
  A := (-8990902065373894363986551 / 5000000000000000000000000)
  B := (49639077942664588949384097 / 1000000000000000000000000000)
  C := (-18355757266140882225102793 / 10000000000000000000000000000)
  dδ := (29657650818470764064738177 / 1000000000000000000000000000)
  dM := (24657572547386670709645973 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(990605456246798410369081 / 31250000000000000000000), (5961865822798378644620243 / 25000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (23 / 48)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell132
