import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (108)
  A := (-11439920284109689652041197 / 10000000000000000000000000)
  B := (15223406465336767473539581 / 250000000000000000000000000)
  C := (-10552479133341036154902781 / 50000000000000000000000000)
  dδ := (18526365546182511911954549 / 500000000000000000000000000)
  dM := (22892815819278877114209547 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(27775958154990902926329 / 2000000000000000000000), (34341558201956004836574721 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301 / 666)
  hi := (17 / 37)
  vmin := (109865 / 443556)
  damping := (109865 / 443556)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell109
