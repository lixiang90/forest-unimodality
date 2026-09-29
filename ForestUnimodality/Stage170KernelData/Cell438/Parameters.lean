import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell438
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (97013525993409021062063857 / 1000000000000000000000000000)
  B := (16561345731426715954803797 / 1000000000000000000000000000)
  C := (-30300218112693677596780617 / 1000000000000000000000000000)
  dδ := (952118162474652391692731 / 62500000000000000000000000)
  dM := (10408821631022660406974689 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1342865367432518330925717 / 312500000000000000000000), (50876535748303943762493873 / 10000000000000000000000000)]
  retention := ![(9 / 20), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell438
