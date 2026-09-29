import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (74)
  A := (-41015546790211792171021443 / 100000000000000000000000000)
  B := (3415851805411512787102879 / 100000000000000000000000000)
  C := (-2906938642414838222527429 / 25000000000000000000000000)
  dδ := (306655612780698354213893 / 12500000000000000000000000)
  dM := (5824318930387357962606687 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(2530078914613606677619373 / 250000000000000000000000), (10866978818547160301477561 / 500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell096
