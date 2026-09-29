import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell306
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (42)
  A := (-10960627169067616577535773 / 500000000000000000000000000)
  B := (8300552883193774295067513 / 500000000000000000000000000)
  C := (18646273937504849460555789 / 500000000000000000000000000)
  dδ := (6235366145533615539475747 / 500000000000000000000000000)
  dM := (44881535405600652311082499 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10320252456590250922374707 / 10000000000000000000000000), (2994571048752040098861471 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell306
