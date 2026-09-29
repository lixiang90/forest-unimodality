import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell333
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (25)
  A := (32708246968455872432102183 / 500000000000000000000000000)
  B := (8888209143992936711597963 / 500000000000000000000000000)
  C := (7396683168227280447126759 / 250000000000000000000000000)
  dδ := (7592207162174620209416087 / 500000000000000000000000000)
  dM := (1543764723100325019942633 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5840848638071928000670141 / 1000000000000000000000000), (12565700211005268460695561 / 5000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 3)
  hi := (35 / 52)
  vmin := (595 / 2704)
  damping := (1487500000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell333
