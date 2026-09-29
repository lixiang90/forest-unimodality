import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell488
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-4523674424001274788054161 / 2500000000000000000000000)
  B := (24371764847900306144579119 / 250000000000000000000000000)
  C := (5979991749999583093913569 / 5000000000000000000000000000)
  dδ := (56957819716135928145295253 / 1000000000000000000000000000)
  dM := (18839186321966759195961627 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(10373614076969678521322749 / 1000000000000000000000000), (45380582166031828705854423 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5227 / 10302)
  hi := (3493 / 6868)
  vmin := (11788875 / 47169424)
  damping := (11788875 / 47169424)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell488
