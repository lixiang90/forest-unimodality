import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell348
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (24269240320357576283782919 / 500000000000000000000000000)
  B := (2702220120786395611556241 / 250000000000000000000000000)
  C := (14313932449900699725442443 / 1000000000000000000000000000)
  dδ := (84274822891866104507263557 / 10000000000000000000000000000)
  dM := (24747283197076617658341849 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6128399621328942115106031 / 12500000000000000000000000), (80163043269640930077457597 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 156)
  hi := (9 / 13)
  vmin := (36 / 169)
  damping := (1440000000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell348
