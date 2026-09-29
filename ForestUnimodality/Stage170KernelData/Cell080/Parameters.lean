import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (58)
  A := (14570211846603408076816777 / 1000000000000000000000000000)
  B := (14595105275673236552846923 / 1000000000000000000000000000)
  C := (-2514048823143457886408747 / 50000000000000000000000000)
  dδ := (3181646030790360492324087 / 250000000000000000000000000)
  dM := (14462837402220594593127423 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(29167627500116974914590173 / 10000000000000000000000000), (10458581421212674200660331 / 500000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell080
