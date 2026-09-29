import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell407
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (-60570821452901462244255981 / 100000000000000000000000000)
  B := (25680331572559788461118657 / 500000000000000000000000000)
  C := (12994892033612884252313791 / 100000000000000000000000000)
  dδ := (31235791600824357877597137 / 1000000000000000000000000000)
  dM := (44291577297409656524887489 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2394918661268369552974633 / 1250000000000000000000000), (11776870642152140078451339 / 500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 93)
  hi := (107 / 187)
  vmin := (8560 / 34969)
  damping := (8560 / 34969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell407
