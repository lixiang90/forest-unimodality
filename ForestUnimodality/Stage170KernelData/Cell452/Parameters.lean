import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell452
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (67)
  A := (-6473848534852015179552609 / 10000000000000000000000000)
  B := (12932909061566034633616873 / 250000000000000000000000000)
  C := (-14655955372390599977805437 / 100000000000000000000000000)
  dδ := (6580251060284351971585437 / 200000000000000000000000000)
  dM := (44206436580973551813550371 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(5295047691246381305063551 / 500000000000000000000000), (4480734559010614681540119 / 250000000000000000000000)]
  retention := ![(3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell452
