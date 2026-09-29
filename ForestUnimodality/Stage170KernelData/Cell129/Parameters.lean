import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (162)
  A := (-2036260006310881194568907 / 1250000000000000000000000)
  B := (1306997314305137769530063 / 20000000000000000000000000)
  C := (-5386557305842875915252721 / 2500000000000000000000000000)
  dδ := (40670018536149717125471881 / 1000000000000000000000000000)
  dM := (9195776534233920896863057 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(2833667495376143818930359 / 500000000000000000000000), (16735101904163581565398999 / 1000000000000000000000000), (13793004970442160583843361 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (23 / 48)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell129
