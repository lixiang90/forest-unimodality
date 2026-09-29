import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell421
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (98726964870755339340746559 / 1000000000000000000000000000)
  B := (5179887467722075686249461 / 250000000000000000000000000)
  C := (5593550104039174929171363 / 125000000000000000000000000)
  dδ := (3878432683422421839436467 / 200000000000000000000000000)
  dM := (1633200530099979770268237 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10034596400621328626812101 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 14)
  hi := (41 / 63)
  vmin := (902 / 3969)
  damping := (902 / 3969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell421
