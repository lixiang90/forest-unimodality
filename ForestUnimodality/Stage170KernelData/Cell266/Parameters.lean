import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell266
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (72)
  A := (-12831186792822082464837763 / 50000000000000000000000000)
  B := (11846467464878896944102671 / 500000000000000000000000000)
  C := (15149619352237342351230609 / 200000000000000000000000000)
  dδ := (8308821736299864049724029 / 500000000000000000000000000)
  dM := (6465033559775118043953107 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(77879514391644866222463861 / 10000000000000000000000000), (4533041624435688987659887 / 200000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 187)
  hi := (27 / 47)
  vmin := (540 / 2209)
  damping := (540 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell266
