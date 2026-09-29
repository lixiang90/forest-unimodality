import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell305
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (40)
  A := (-38879402260975516316676703 / 1000000000000000000000000000)
  B := (2158015528687668924123777 / 100000000000000000000000000)
  C := (23862293736326752741083723 / 500000000000000000000000000)
  dδ := (408854491753074100052201 / 25000000000000000000000000)
  dM := (14063246414897515924359583 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(152080566152852423300601 / 10000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129 / 209)
  hi := (33 / 53)
  vmin := (660 / 2809)
  damping := (660 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell305
