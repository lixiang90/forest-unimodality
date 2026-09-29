import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (104)
  A := (-65471919258198256862613107 / 100000000000000000000000000)
  B := (4360712105421644599334563 / 125000000000000000000000000)
  C := (12602092218733876305414299 / 100000000000000000000000000)
  dδ := (2774380111941259115238001 / 125000000000000000000000000)
  dM := (19800460239337508774881691 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10942065028132805792893123 / 1000000000000000000000000), (8749145712477551128927189 / 250000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 89)
  hi := (99 / 179)
  vmin := (7920 / 32041)
  damping := (7920 / 32041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell233
