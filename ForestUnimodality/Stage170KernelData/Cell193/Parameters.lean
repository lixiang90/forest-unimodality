import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell193
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (137)
  A := (-4675350530597942425004021 / 2500000000000000000000000)
  B := (4053090205948146895753581 / 50000000000000000000000000)
  C := (16274682519426388136590811 / 5000000000000000000000000000)
  dδ := (46893664419887709504664031 / 1000000000000000000000000000)
  dM := (2548160465620759665417161 / 4000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(8867366884543315563860233 / 250000000000000000000000), (3984670540866862324946851 / 40000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111 / 211)
  hi := (28 / 53)
  vmin := (700 / 2809)
  damping := (700 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell193
