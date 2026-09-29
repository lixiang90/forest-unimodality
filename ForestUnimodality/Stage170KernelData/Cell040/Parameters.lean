import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (37)
  A := (8140474766891667657731091 / 50000000000000000000000000)
  B := (76913334217943041953846617 / 10000000000000000000000000000)
  C := (-15554792087450702506301603 / 1000000000000000000000000000)
  dδ := (79532524299747199558741073 / 10000000000000000000000000000)
  dM := (25731408863807886784830573 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(96010535288035029566344747 / 1000000000000000000000000)]
  retention := ![(3 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell040
