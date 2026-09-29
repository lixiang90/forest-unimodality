import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell313
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (33)
  A := (15790872963628510285971629 / 250000000000000000000000000)
  B := (11168380263849484249072397 / 500000000000000000000000000)
  C := (51435335162215559123843889 / 1000000000000000000000000000)
  dδ := (19902291729511759066362231 / 1000000000000000000000000000)
  dM := (4260539326080907916987489 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6111147042993712474867607 / 500000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell313
