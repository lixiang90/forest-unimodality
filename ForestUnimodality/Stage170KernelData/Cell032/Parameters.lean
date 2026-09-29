import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (33)
  A := (244535570321882856165141 / 1562500000000000000000000)
  B := (80055764491884801731247379 / 10000000000000000000000000000)
  C := (-7277340028780609169911653 / 500000000000000000000000000)
  dδ := (82956867249750453063850131 / 10000000000000000000000000000)
  dM := (27466056835547374430535339 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(32860973758664442812005291 / 1000000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 63)
  hi := (13 / 42)
  vmin := (836 / 3969)
  damping := (33440000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell032
