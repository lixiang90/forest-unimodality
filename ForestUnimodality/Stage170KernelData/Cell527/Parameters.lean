import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell527
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (109)
  A := (-9071904995783550368315673 / 5000000000000000000000000)
  B := (1075785520218637131284467 / 10000000000000000000000000)
  C := (15627832383197190480039751 / 50000000000000000000000000)
  dδ := (29278195491090730495642447 / 500000000000000000000000000)
  dM := (10322998363698340437699663 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(13480447204821524920248521 / 2000000000000000000000000), (41537255322749345509691921 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 54)
  hi := (643 / 1188)
  vmin := (350435 / 1411344)
  damping := (350435 / 1411344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell527
