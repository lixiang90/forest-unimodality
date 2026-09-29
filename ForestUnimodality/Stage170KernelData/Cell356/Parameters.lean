import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell356
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (26)
  A := (6706782528638228158435197 / 50000000000000000000000000)
  B := (6930668136112646399160653 / 500000000000000000000000000)
  C := (-23604739581716046442627643 / 1000000000000000000000000000)
  dδ := (6897790413748237925428697 / 500000000000000000000000000)
  dM := (76151080706996339625761139 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(21272064871459664403552381 / 25000000000000000000000000), (18535506340760208310314283 / 5000000000000000000000000), (35863805147712080056976447 / 10000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 63)
  hi := (13 / 42)
  vmin := (836 / 3969)
  damping := (33440000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell356
