import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell328
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (34)
  A := (91005796451237473974060777 / 1000000000000000000000000000)
  B := (10274286146287009077737729 / 1000000000000000000000000000)
  C := (5181861571428495946700643 / 250000000000000000000000000)
  dδ := (18295359792242088525782151 / 2000000000000000000000000000)
  dM := (9297636643774140948609519 / 200000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(45554639926896420831781143 / 10000000000000000000000000), (73786925505956340032298613 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 63)
  hi := (83 / 126)
  vmin := (3569 / 15876)
  damping := (35690000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell328
