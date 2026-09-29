import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (73)
  A := (-23649117318800460084915471 / 100000000000000000000000000)
  B := (12351558922311958038653401 / 500000000000000000000000000)
  C := (-87813625489644650534692971 / 1000000000000000000000000000)
  dδ := (9479696356177558930200533 / 500000000000000000000000000)
  dM := (893519933735508727144347 / 6250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(596062212420352399711021 / 31250000000000000000000), (12072951089590093332049037 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65 / 153)
  hi := (22 / 51)
  vmin := (5720 / 23409)
  damping := (5720 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell093
