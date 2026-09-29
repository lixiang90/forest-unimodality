import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (54)
  A := (18145468440207196447744309 / 5000000000000000000000000000)
  B := (8558808311772489116342477 / 500000000000000000000000000)
  C := (-57686102061875944857494147 / 1000000000000000000000000000)
  dδ := (3729564269735550618295461 / 250000000000000000000000000)
  dM := (97608138879371373025466141 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(21042567421215010448065641 / 10000000000000000000000000), (20062072110072779906886353 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell079
