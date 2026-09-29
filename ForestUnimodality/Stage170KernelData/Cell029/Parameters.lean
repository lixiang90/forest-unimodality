import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (1481551151637707330976923 / 10000000000000000000000000)
  B := (575590521801077822927617 / 50000000000000000000000000)
  C := (-5069244179000930057565899 / 250000000000000000000000000)
  dδ := (1467659484611737305201351 / 125000000000000000000000000)
  dM := (27184651920516613045732471 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(16922804685173189476188327 / 5000000000000000000000000), (26991262961015412003007441 / 5000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell029
