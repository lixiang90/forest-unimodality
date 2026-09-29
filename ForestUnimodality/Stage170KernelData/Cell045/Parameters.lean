import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (40)
  A := (15252684852306431674051623 / 100000000000000000000000000)
  B := (15858078568571645772244949 / 2000000000000000000000000000)
  C := (-8180262207927545617391907 / 500000000000000000000000000)
  dδ := (3958487811158934409350163 / 500000000000000000000000000)
  dM := (1055823937847794220801223 / 40000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(2095681845826854328151967 / 20000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 126)
  hi := (1 / 3)
  vmin := (3485 / 15876)
  damping := (34850000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell045
