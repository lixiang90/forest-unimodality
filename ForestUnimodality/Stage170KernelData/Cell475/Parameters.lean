import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell475
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-411337414683096001198237 / 200000000000000000000000)
  B := (278988566281853263284507 / 2500000000000000000000000)
  C := (-1662714185537093045715723 / 1250000000000000000000000000)
  dδ := (59921273106547504050389819 / 1000000000000000000000000000)
  dM := (11215052232237232143069461 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16910793151889724761360867 / 5000000000000000000000000), (92502573194448444837689749 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9529 / 19404)
  hi := (4777 / 9702)
  vmin := (94098875 / 376515216)
  damping := (94098875 / 376515216)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell475
