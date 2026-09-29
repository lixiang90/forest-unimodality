import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell368
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (-18846012449242933719517623 / 1000000000000000000000000000)
  B := (20597430553090347732370091 / 1000000000000000000000000000)
  C := (-61149814522601861344064389 / 1000000000000000000000000000)
  dδ := (17466512313097901781810961 / 1000000000000000000000000000)
  dM := (3351537124128545468842999 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(96417656569492766749363 / 20000000000000000000000), (14065978557730611342435623 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101 / 255)
  hi := (103 / 255)
  vmin := (15554 / 65025)
  damping := (15554 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell368
