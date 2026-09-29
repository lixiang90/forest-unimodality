import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell492
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-4681701956801047451151021 / 2500000000000000000000000)
  B := (12434986839870161567933593 / 125000000000000000000000000)
  C := (287359824701372193044447 / 156250000000000000000000000)
  dδ := (11183199791859099736512917 / 200000000000000000000000000)
  dM := (96045831249861744922935447 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3175552269587400999739657 / 400000000000000000000000), (5820898227951866843454809 / 62500000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381 / 10506)
  hi := (10787 / 21012)
  vmin := (110297075 / 441504144)
  damping := (110297075 / 441504144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell492
