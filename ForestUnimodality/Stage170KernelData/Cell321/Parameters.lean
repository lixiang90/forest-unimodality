import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell321
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (29)
  A := (19829622414769046137017483 / 250000000000000000000000000)
  B := (2418440464998733961665689 / 125000000000000000000000000)
  C := (40381829402230534631357273 / 1000000000000000000000000000)
  dδ := (17307175041988771130307967 / 1000000000000000000000000000)
  dM := (14063945428428395738491841 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1037878234235771124360781 / 100000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 14)
  hi := (41 / 63)
  vmin := (902 / 3969)
  damping := (902 / 3969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell321
