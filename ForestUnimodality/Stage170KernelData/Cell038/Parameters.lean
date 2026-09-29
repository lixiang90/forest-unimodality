import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (32)
  A := (3367691596788448510579883 / 25000000000000000000000000)
  B := (2579412185462566422383679 / 250000000000000000000000000)
  C := (-606221132690726565578343 / 31250000000000000000000000)
  dδ := (5043799727127268837933993 / 500000000000000000000000000)
  dM := (5548157857419343565988281 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(79179010253464747748353147 / 10000000000000000000000000), (6500070939548289183917973 / 2500000000000000000000000)]
  retention := ![(3 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (20 / 63)
  hi := (41 / 126)
  vmin := (860 / 3969)
  damping := (34400000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell038
