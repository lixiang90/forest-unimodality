import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell519
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-2065891287605298766152373 / 1000000000000000000000000)
  B := (5487925048653637810636141 / 50000000000000000000000000)
  C := (43174635744685002300413679 / 10000000000000000000000000000)
  dδ := (14694065237958176678434441 / 250000000000000000000000000)
  dM := (2164095202373166396125903 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(30854046223364663958932397 / 5000000000000000000000000), (22927212667586097438743309 / 250000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881 / 45156)
  hi := (11953 / 22578)
  vmin := (127000625 / 509766084)
  damping := (127000625 / 509766084)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell519
