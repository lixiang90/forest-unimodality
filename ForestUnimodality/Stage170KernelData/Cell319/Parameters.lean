import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell319
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (36)
  A := (10940508124202860398277437 / 250000000000000000000000000)
  B := (14338467756343859643708427 / 1000000000000000000000000000)
  C := (7328779028213250855416927 / 250000000000000000000000000)
  dδ := (1151680802032472444862421 / 100000000000000000000000000)
  dM := (18838759875000600735404227 / 250000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5977493093316981198626081 / 5000000000000000000000000), (2976792986980360655735467 / 250000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236 / 371)
  hi := (9 / 14)
  vmin := (45 / 196)
  damping := (45 / 196)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell319
