import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (50)
  A := (10229506873750940865619441 / 50000000000000000000000000)
  B := (753171186242727885851167 / 80000000000000000000000000)
  C := (-2094283856180137372987593 / 62500000000000000000000000)
  dδ := (10445564354223096231732981 / 1000000000000000000000000000)
  dM := (3969579577536870150945153 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(40412356963119497876846253 / 10000000000000000000000000), (15531175040992488689539641 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 255)
  hi := (33 / 85)
  vmin := (15326 / 65025)
  damping := (15326 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell069
