import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (23)
  A := (4081416464108603398219799 / 25000000000000000000000000)
  B := (10619501657883969464313267 / 1000000000000000000000000000)
  C := (-1929301457380318100820471 / 125000000000000000000000000)
  dδ := (2996184569755728534234951 / 250000000000000000000000000)
  dM := (8874985680323590434438047 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(71588780763362780401593 / 3125000000000000000000)]
  retention := ![(1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 4)
  hi := (9 / 35)
  vmin := (3 / 16)
  damping := (7500000000000000000000000000000000000000 / 98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell000
