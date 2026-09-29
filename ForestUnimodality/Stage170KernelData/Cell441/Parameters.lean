import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell441
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (32)
  A := (290761163109512075237717 / 2000000000000000000000000)
  B := (18157472401886084328870297 / 1000000000000000000000000000)
  C := (-10586993018436659588776827 / 250000000000000000000000000)
  dδ := (9013201068518710001864491 / 500000000000000000000000000)
  dM := (6191083153255362396538697 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(2971397411841988217551247 / 12500000000000000000000000), (9219785899644267201935577 / 5000000000000000000000000), (23557387694012534851140117 / 2500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89 / 255)
  hi := (91 / 255)
  vmin := (14774 / 65025)
  damping := (14774 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell441
