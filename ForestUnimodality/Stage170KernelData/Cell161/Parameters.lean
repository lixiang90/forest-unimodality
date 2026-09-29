import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (263)
  A := (-9014964415490641319550491 / 5000000000000000000000000)
  B := (3098405147917184399714019 / 62500000000000000000000000)
  C := (54177981851009817792358403 / 100000000000000000000000000000)
  dδ := (1437138458540100464932987 / 50000000000000000000000000)
  dM := (309533421868191834500951 / 1250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1768351890438877305200549 / 50000000000000000000000), (5645044457969294171562069 / 25000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51 / 101)
  hi := (26 / 51)
  vmin := (650 / 2601)
  damping := (650 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell161
