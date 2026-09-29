import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell549
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (30)
  A := (3361269741895502288997477 / 25000000000000000000000000)
  B := (11168160813913129494889809 / 500000000000000000000000000)
  C := (58903002787524756656001301 / 1000000000000000000000000000)
  dδ := (23194844055216091299742587 / 1000000000000000000000000000)
  dM := (19105190696958214424672207 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2792740331395602293440561 / 250000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467 / 742)
  hi := (236 / 371)
  vmin := (31860 / 137641)
  damping := (31860 / 137641)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell549
