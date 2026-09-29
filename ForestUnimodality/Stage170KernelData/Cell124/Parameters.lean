import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (164)
  A := (-2878352909891851532080409 / 2000000000000000000000000)
  B := (14900051106877081064094881 / 250000000000000000000000000)
  C := (-1312706828012013193437979 / 500000000000000000000000000)
  dδ := (10045132517164878649396087 / 250000000000000000000000000)
  dM := (4162221361481480944206901 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(10312968441733611157928863 / 1000000000000000000000000), (15221030998665776223788271 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 47)
  hi := (9 / 19)
  vmin := (550 / 2209)
  damping := (550 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell124
