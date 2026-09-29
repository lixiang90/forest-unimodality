import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell278
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (-9156915477718785056460149 / 50000000000000000000000000)
  B := (1544465439022333535026843 / 62500000000000000000000000)
  C := (7092854960386536788963241 / 100000000000000000000000000)
  dδ := (8905593591610977063921517 / 500000000000000000000000000)
  dM := (15559765449283822959930523 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(41162234702338320602166277 / 10000000000000000000000000), (19361908483424695504027113 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 12)
  hi := (53 / 90)
  vmin := (1961 / 8100)
  damping := (1961 / 8100)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell278
