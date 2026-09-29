import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell256
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (77)
  A := (-30869112814445475278191111 / 100000000000000000000000000)
  B := (1006688951757266359265941 / 40000000000000000000000000)
  C := (5198690946374168002364069 / 62500000000000000000000000)
  dδ := (17395022105660032374352397 / 1000000000000000000000000000)
  dM := (3459258854370689668629793 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(219991604080252267650053 / 25000000000000000000000), (963535117147804243131759 / 40000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21 / 37)
  hi := (53 / 93)
  vmin := (2120 / 8649)
  damping := (2120 / 8649)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell256
