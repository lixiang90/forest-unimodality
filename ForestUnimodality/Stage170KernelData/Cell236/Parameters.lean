import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell236
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (86)
  A := (-20489539424639689496387973 / 25000000000000000000000000)
  B := (10553952826383830587708701 / 200000000000000000000000000)
  C := (203308233817239489282791 / 1250000000000000000000000)
  dδ := (16156139812154763496510057 / 500000000000000000000000000)
  dM := (2515014056900437839216049 / 6250000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(303249586927035519323681 / 2000000000000000000000000), (20007215706001794330859411 / 1000000000000000000000000), (17262383246815112158856209 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99 / 179)
  hi := (5 / 9)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell236
