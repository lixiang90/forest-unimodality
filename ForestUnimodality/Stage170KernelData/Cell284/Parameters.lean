import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell284
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (-53885352555016131628207177 / 1000000000000000000000000000)
  B := (15982505390110937626424459 / 1000000000000000000000000000)
  C := (12361296099208883211839627 / 250000000000000000000000000)
  dδ := (6258603666588685894567323 / 500000000000000000000000000)
  dM := (4756382961465091629255867 / 62500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6484586773094670242301163 / 500000000000000000000000), (2398553297460681577035757 / 200000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 90)
  hi := (107 / 180)
  vmin := (7811 / 32400)
  damping := (7811 / 32400)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell284
