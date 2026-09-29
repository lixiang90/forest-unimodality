import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (108)
  A := (-7145223948660632490259559 / 5000000000000000000000000)
  B := (7318084474576931619527187 / 100000000000000000000000000)
  C := (2721090441763533360197691 / 12500000000000000000000000)
  dδ := (38724130692614509852145233 / 1000000000000000000000000000)
  dM := (57045969247359446484268997 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2047009208142103187100247 / 125000000000000000000000), (31483934724551897232913689 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643 / 1188)
  hi := (6 / 11)
  vmin := (30 / 121)
  damping := (30 / 121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell217
