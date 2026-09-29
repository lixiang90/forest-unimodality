import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell535
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (63)
  A := (-3760232306720818434797593 / 5000000000000000000000000)
  B := (61767439013531322267169799 / 1000000000000000000000000000)
  C := (3057786556592088644812577 / 20000000000000000000000000)
  dδ := (717721043015599191594589 / 20000000000000000000000000)
  dM := (57990086772391046671115689 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(25539885197213827439099987 / 1000000000000000000000000), (91060730928771249637065921 / 100000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 23)
  hi := (21 / 37)
  vmin := (336 / 1369)
  damping := (336 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell535
