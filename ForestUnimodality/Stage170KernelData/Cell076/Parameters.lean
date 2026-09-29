import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (54)
  A := (155401014109381583345737 / 2000000000000000000000000)
  B := (13374687598502847662995663 / 1000000000000000000000000000)
  C := (-45597373413582768797436273 / 1000000000000000000000000000)
  dδ := (12457621409774258247615819 / 1000000000000000000000000000)
  dM := (32826041870877682932530761 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(537037887119311374561903 / 200000000000000000000000), (957311539125863220078827 / 50000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101 / 255)
  hi := (103 / 255)
  vmin := (15554 / 65025)
  damping := (15554 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell076
