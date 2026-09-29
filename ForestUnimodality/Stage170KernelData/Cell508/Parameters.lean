import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell508
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-5079115699624255744737411 / 2500000000000000000000000)
  B := (10725393361469054420709313 / 100000000000000000000000000)
  C := (16142292347103438365091277 / 5000000000000000000000000000)
  dδ := (28527656013293836712030327 / 500000000000000000000000000)
  dM := (2100109335248813262342349 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(41811807604271606919610349 / 5000000000000000000000000), (3622087013829551551680197 / 40000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294 / 4389)
  hi := (1531 / 2926)
  vmin := (2135745 / 8561476)
  damping := (2135745 / 8561476)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell508
