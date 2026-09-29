import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell461
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-17279144478116336591710933 / 10000000000000000000000000)
  B := (98359042752569264544959537 / 1000000000000000000000000000)
  C := (-42614853105526640658640147 / 10000000000000000000000000000)
  dδ := (29797368176190958816151877 / 500000000000000000000000000)
  dM := (49391694655800185299182603 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(519565634793451636141981 / 62500000000000000000000), (43951856072226192395646649 / 500000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1687 / 3572)
  hi := (9 / 19)
  vmin := (3179995 / 12759184)
  damping := (3179995 / 12759184)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell461
