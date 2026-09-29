import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell479
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-20347708689760261491130677 / 10000000000000000000000000)
  B := (10620610148819564777511459 / 100000000000000000000000000)
  C := (-11705329133443237357020683 / 50000000000000000000000000000)
  dδ := (5636878463783778769879973 / 100000000000000000000000000)
  dM := (1030573735527375240153547 / 1000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3082327038476270875122509 / 2000000000000000000000000), (97367940933730665165057871 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (131 / 264)
  hi := (197 / 396)
  vmin := (17423 / 69696)
  damping := (17423 / 69696)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell479
