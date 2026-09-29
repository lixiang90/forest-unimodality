import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell494
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-4468516636116805332257229 / 2500000000000000000000000)
  B := (3054249027029593607091007 / 31250000000000000000000000)
  C := (214787579990973788446329 / 100000000000000000000000000)
  dδ := (29012165644327698316162767 / 500000000000000000000000000)
  dM := (95198598771114629774753313 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(92164872156612140940978861 / 10000000000000000000000000), (2298505991860083241817847 / 25000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (21967 / 42642)
  vmin := (454167725 / 1818340164)
  damping := (454167725 / 1818340164)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell494
