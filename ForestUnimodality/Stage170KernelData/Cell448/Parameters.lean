import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell448
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (49)
  A := (-11500451902434648403517059 / 125000000000000000000000000)
  B := (1552517923180591870660483 / 62500000000000000000000000)
  C := (-37360420559514981309057191 / 500000000000000000000000000)
  dδ := (20220739060620291499548173 / 1000000000000000000000000000)
  dM := (17658042949614128204298413 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(41282358908144081155455751 / 10000000000000000000000000), (15861299502021758200953627 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell448
