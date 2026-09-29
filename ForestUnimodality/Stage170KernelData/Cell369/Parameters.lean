import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell369
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (51)
  A := (-8024135629044213622762527 / 200000000000000000000000000)
  B := (4239047635754065318502981 / 200000000000000000000000000)
  C := (-16737327128419108440704477 / 250000000000000000000000000)
  dδ := (17750194978077067642363573 / 1000000000000000000000000000)
  dM := (868637505282437491071091 / 6250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(11173319907409733353631509 / 10000000000000000000000000), (16610717880696752590807819 / 10000000000000000000000000), (9048393019776188594960331 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103 / 255)
  hi := (7 / 17)
  vmin := (15656 / 65025)
  damping := (15656 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell369
