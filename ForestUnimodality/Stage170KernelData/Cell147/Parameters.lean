import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (274)
  A := (-17795445948772571809115561 / 10000000000000000000000000)
  B := (6102624973707827978064433 / 125000000000000000000000000)
  C := (-51349915779631491192375181 / 100000000000000000000000000000)
  dδ := (29130207065647558545284923 / 1000000000000000000000000000)
  dM := (24083353522123880532772311 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(9532758399045558661555333 / 250000000000000000000000), (468121630202065603043593 / 2000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24 / 49)
  hi := (49 / 99)
  vmin := (600 / 2401)
  damping := (600 / 2401)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell147
