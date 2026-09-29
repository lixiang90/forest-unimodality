import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (45)
  A := (930611871185495814806643 / 5000000000000000000000000)
  B := (5129954767614942900966213 / 500000000000000000000000000)
  C := (-7468958318732072353129947 / 250000000000000000000000000)
  dδ := (10702708429357301461726237 / 1000000000000000000000000000)
  dM := (5461815643455723258620823 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(98753887174392679382251 / 7812500000000000000000), (8539524313126982235644391 / 2000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31 / 85)
  hi := (19 / 51)
  vmin := (1674 / 7225)
  damping := (1674 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell061
