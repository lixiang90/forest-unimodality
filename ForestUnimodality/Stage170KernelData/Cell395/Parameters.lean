import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell395
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (113)
  A := (-19999836482406225146490897 / 10000000000000000000000000)
  B := (6111192665589708881979103 / 62500000000000000000000000)
  C := (39822379379754980696648481 / 10000000000000000000000000000)
  dδ := (26424498696332923003415871 / 500000000000000000000000000)
  dM := (5523860866133978975807059 / 6250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1994097741115330668648653 / 125000000000000000000000), (94998377663382044033824059 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113 / 213)
  hi := (57 / 107)
  vmin := (2850 / 11449)
  damping := (2850 / 11449)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell395
