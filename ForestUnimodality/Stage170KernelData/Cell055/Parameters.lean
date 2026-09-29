import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (37)
  A := (3671406134552173328344793 / 20000000000000000000000000)
  B := (2688643143308462948870563 / 200000000000000000000000000)
  C := (-7279592501637392742974697 / 200000000000000000000000000)
  dδ := (2845103252869825294357753 / 200000000000000000000000000)
  dM := (18484662944177897742374303 / 250000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(13903175236264315728362817 / 5000000000000000000000000), (2711609856942330587514789 / 250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (91 / 255)
  hi := (31 / 85)
  vmin := (14924 / 65025)
  damping := (14924 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell055
