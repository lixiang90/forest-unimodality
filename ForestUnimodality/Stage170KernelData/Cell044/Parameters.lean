import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (38)
  A := (3622500152422218872239057 / 25000000000000000000000000)
  B := (75325873200716882138738839 / 10000000000000000000000000000)
  C := (-1554249819506217655806779 / 100000000000000000000000000)
  dδ := (75211268412018568094157267 / 10000000000000000000000000000)
  dM := (25075818523885331617342617 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(99544887670713990246440517 / 1000000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 126)
  hi := (1 / 3)
  vmin := (3485 / 15876)
  damping := (34850000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell044
